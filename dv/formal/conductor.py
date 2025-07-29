import asyncio
import re
import subprocess
import time
import json
import os
from math import floor
from types import CoroutineType
from typing import Any, Coroutine, TypeVar

def global_memory_free():
    with open("/proc/meminfo", "r") as f:
        c = f.read()
        for line in c.split("\n"):
            if line.startswith("MemFree:"):
                return float(line[8:-2].strip()) / (1024 * 1024)
    return 0

expected_memory_free = global_memory_free()

class ProcessFuture(asyncio.Future):
    def __init__(self, loop, proc):
        super().__init__(loop=loop)
        self.proc = proc

    def cancel(self, msg = None):
        self.proc.kill()
        return super().cancel(msg=msg)

class Process:
    def __init__(self, cmd, expected_memory = None, expected_time = None, timeout = None, killer = None, debug_slow = None):
        self.cmd = cmd
        self.expected_memory = expected_memory or 0
        self.expected_time = expected_time or 0
        self.timeout = timeout
        self.killer = killer if killer is not None else Killer()

        self.debug_slow = debug_slow
        self.debug_slow_count = 0

        self.proc = None

        self.future: asyncio.Future[tuple[int | None, float, float, str]] = ProcessFuture(asyncio.get_running_loop(), self)

        self.max_memory = 0
        self.start_time = 0

    def start(self):
        print("$", self.cmd)
        self.proc = subprocess.Popen(self.cmd, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.start_time = time.time()
        self.max_memory = 0

    def kill(self):
        self.killer.kill()

    def poll(self):
        global expected_memory_free
        assert self.proc is not None

        dt = time.time() - self.start_time
        code = self.proc.poll()
        if code is not None and self.killer.kill_ == 0:
            print(f"Finished `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            if not self.future.cancelled():
                self.future.set_result((code, self.max_memory, dt, "OK"))
            return True
        elif self.killer.kill_ == 2:
            print(gray(f"Kill (will restart) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)"))
            self.proc.kill()
            self.killer.kill_ = 0
            self.expected_memory = max(self.expected_memory, self.max_memory)
            self.expected_time = max(self.expected_time, dt)
            return True
        elif self.timeout is not None and dt > self.timeout:
            print(f"Kill `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result((None, self.max_memory, dt, "TIMEOUT"))
            return True
        elif self.killer.kill_ == 1:
            print(gray(f"Kill (uninterested) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)"))
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result((None, self.max_memory, dt, "UNINTERESTED"))
            return True

        with open(f"/proc/{self.proc.pid}/status", "r") as f:
            c = f.read()
            for line in c.split("\n"):
                if line.startswith("RssAnon:"):
                    mem = float(line[8:-2].strip()) / (1024 * 1024)
                    self.max_memory = max(mem, self.max_memory)
                    break

        n = floor(dt / 60.0)
        if n > self.debug_slow_count:
            if self.debug_slow is not None:
                self.debug_slow(dt)
            self.debug_slow_count = n
        
        return False

class ProcessRunner:
    GLOBAL_MEMORY_BUFFER = 5
    POLL_DELAY = 0.1
    MAX_RUNNING = len(os.sched_getaffinity(0)) - 2
    
    def __init__(self):
        self.pending = []
        self.running = []
        # self.churn = 0
        self.first_start = 0

    def append(self, proc):
        # FIXME: Use a deque
        self.pending.insert(0, proc)

    def start_loop(self):
        asyncio.get_running_loop().call_soon(lambda: self.poll())

    def poll(self):
        # Kill recently started processes until memory is OK
        free = global_memory_free()
        while free < ProcessRunner.GLOBAL_MEMORY_BUFFER and len(self.running) > 0:
            last = self.running.pop()
            last.killer.kill_restart()
            free += max(last.max_memory, 3)
            last.poll()
            self.pending.append(last)

            # self.churn += 1
            # print("Killed, churn rate =", self.churn / (time.time() - self.first_start))

        while len(self.running) < ProcessRunner.MAX_RUNNING and len(self.pending) > 0 and free > self.pending[-1].expected_memory + ProcessRunner.GLOBAL_MEMORY_BUFFER:
            if self.first_start == 0:
                self.first_start = time.time()
            last = self.pending.pop()
            last.start()
            free -= max(last.expected_memory, 3) # otherwise lots of zeros won't help
            self.running.append(last)

        p = 0
        while p < len(self.running):
            if self.running[p].poll():
                self.running.pop(p)
            else:
                p += 1

        asyncio.get_running_loop().call_later(ProcessRunner.POLL_DELAY, lambda: self.poll())
print(f"Process runner will have a maximum of {ProcessRunner.MAX_RUNNING} processes")

class Killer:
    def __init__(self):
        self.kill_ = 0

    # Kill because we don't care about the result
    def kill(self):
        self.kill_ = 1

    # Kill because we have to now, but we will try again later
    def kill_restart(self):
        self.kill_ = 2

process_runner = ProcessRunner()

async def shell(cmd, expected_memory = None, timeout = None, killer = None, debug_slow = None):
    proc = Process(cmd, expected_memory=expected_memory, timeout=timeout, killer=killer, debug_slow=debug_slow)
    process_runner.append(proc)
    return await proc.future

SOURCE = "build/noprops.aig"

# This (the result of aig-manip optimise) is far slower and more memory taxing to work with, so it should not be used
# SOURCE = "build/noprops.opt.aig"

aiger_idx = 0
async def prepare_aiger(step, props):
    global aiger_idx

    name = f"build/aiger-{aiger_idx}.aig"
    aiger_idx += 1
    assert (await shell(
        f"./aig-manip/target/release/aig-manip {SOURCE} {name} select build/noprops.aig.map {step} {' '.join(props)}",
        expected_memory=0.5
    ))[0] == 0

    return name

def green(s): return f"\033[32;1m{s}\033[0m"
def red(s): return f"\033[31;1m{s}\033[0m"
def white(s): return f"\033[1m{s}\033[0m"
def orange(s): return f"\033[33;1m{s}\033[0m"
def gray(s): return f"\033[90m{s}\033[0m"

def proof_done(engine_config, step, props, results):
    code, mem, time, reason = results
    mem = mem or 0.0
    time = time or 0.0
    match code:
        case 20:
            print(green(f"UNSAT: {len(props)} properties in step {step} proven in {time:.3f}s with {mem:.3f}GB"))
            return "OK"
        case -9:
            print(red(f"KILLED by OS: Failed to prove {len(props)} properties in step {step} ({time:.3f}s with {mem:.3f}GB)"))
            return "KILL"
        case None:
            print(red(f"TIMEOUT: Failed to prove {len(props)} properties in step {step} ({time:.3f}s with {mem:.3f}GB)"))
            return "TIMEOUT"
        case n:
            print(red(f"Unknown Exit Code {n}: Failed to prove {len(props)} properties in step {step} ({time:.3f}s with {mem:.3f}GB)"))
            return "UNKNOWN"

async def prove(engine_config, step, props, timeout=None, expected_memory=None):
    specialised = await prepare_aiger(step, props)
    res = await shell(f"{engine_config} {specialised}", timeout=timeout, expected_memory=expected_memory)
    proof_done(engine_config, step, props, res)
    return res

STANDARD_ENGINES = [
    ("rIC3", 10),
    ("rIC3 -e kind", 10),
    # ("rIC3 --no-preproc", 20),
    ("rIC3 -e kind --no-preproc", 10)
]

class RaceWonException(Exception):
    def __init__(self, result):
        super().__init__()
        self.result = result

def won_race(result):
    raise RaceWonException(result)

async def race(tasks):
    winner = None
    try:
        async with asyncio.TaskGroup() as tg:
            for task in tasks:
                tg.create_task(task)
    except* RaceWonException as e:
        for result in e.exceptions:
            winner = result.result
    return winner

def while_running(coro, f, timer):
    loop = asyncio.get_running_loop()
    task = loop.create_task(coro)
    def event():
        if not task.done():
            f()
            loop.call_later(timer, event)
    loop.call_later(timer, event)
    return task

async def explore(step, props, timeout=None, configs=None, debug_slow=None) -> asyncio.Future[None | tuple[str, tuple[int, float, float, str]]]:
    specialised = await prepare_aiger(step, props)

    async def explore_one(engine_config, idx, expected_memory):
        result = await shell(f"{engine_config} {specialised}", timeout=timeout, expected_memory=expected_memory, debug_slow=debug_slow)
        proof_done(engine_config, step, props, result)
        if result[0] in {10, 20}:
            won_race((engine_config, result))
    
    return await race([explore_one(config, idx, mem) for idx, (config, mem) in enumerate(STANDARD_ENGINES if configs is None else configs)])

async def build_strategy_rec(step, prop_tree, eager=False):
    def find_all(prop_tree, all_props):
        for prop in prop_tree:
            if type(prop) == str:
                all_props.append(prop)
            else:
                find_all(prop, all_props)
    all_props = []
    find_all(prop_tree, all_props)

    ENGINES = [
        # ("rIC3", 10),
        # ("rIC3 --no-preproc", 20),
        ("rIC3 -e kind --no-preproc", 10),
        # ("rIC3 -e kind", 10)
    ]

    if len(all_props) == 0:
        return []

    if len(all_props) == 1:
        while True:
            res = await explore(step, all_props, timeout=300.0, configs=ENGINES, debug_slow=lambda dt: print(gray(f"Still exploring step {step} property {all_props[0]} ({dt:.3f}s)")))
            if res is not None:
                print(green(f"Constructed proof for 1 property in step {step}: {all_props[0]}"))
                return [(step, all_props, res[0], res[1])]
            print(red(f"Failed to find proof for property in step {step}: {all_props[0]} - ignoring"))
            return []

    if len(prop_tree) == 1:
        return await build_strategy_rec(step, prop_tree[0])

    async def without_split():
        res = await explore(step, all_props, timeout=120.0, configs=ENGINES)
        if res is not None:
            print(green(f"Constructed proof for {len(all_props)} properties in step {step}: {' '.join(all_props)}"))
            won_race([(step, all_props, res[0], res[1])])

    async def with_split():
        children = []
        rest = []
        for prop in prop_tree:
            if type(prop) == str:
                rest.append(prop)
            else:
                children.append(prop)

        if not eager:
            await asyncio.sleep(120.0) # Give the rest a head start
        else:
            await asyncio.sleep(20.0) # Give the rest a tiny head start anyway

        if len(children) == 0:
            solutions = await asyncio.gather(*[build_strategy_rec(step, [child]) for child in rest])
        else:
            children.append(rest)
            solutions = await asyncio.gather(*[build_strategy_rec(step, tree) for tree in children])
        flattened = []
        for solution in solutions:
            flattened.extend(solution)
        won_race(flattened)

    return await race([without_split(), with_split()])

async def run_strategy(strategy):
    proofs = []
    strategy.sort(key=lambda x: x[3][2], reverse=True)
    for step in strategy:
        proofs.append(prove(step[2], step[0], step[1], expected_memory=step[3][1] * 1.1))
    return await asyncio.gather(*proofs)

def split_by_prefixes(names):
    def chunk_name(name):
        nts = lambda x: "" if x is None else x
        split = re.split(r"_([A-Z])|_|([A-Z])", name)
        return ([split[0]] if split[0] != "" else []) + [nts(split[i + 1]) + nts(split[i + 2]) + split[i + 3] for i in range(0, len(split) - 1, 3)]

    def group(props):
        buckets = {}
        done = []
        for chunks, name in props:
            if len(chunks) == 1:
                done.append(name)
            elif chunks[0] not in buckets:
                buckets[chunks[0]] = [(chunks[1:], name)]
            else:
                buckets[chunks[0]].append((chunks[1:], name))
        for pre in buckets:
            bucket = group(buckets[pre])
            # while len(bucket) == 1:
            #     bucket = bucket[0]
            done.append(bucket)
        return done
            
    chunked_names = [(chunk_name(name), name) for name in names]
    return group(chunked_names)

SKIPPED_PROPS = [
    (1, "Ibex_SpecPastReg"),
    (1, "Ibex_SpecPastWbexc_Mcause"),
    (1, "Ibex_SpecPastWbexc_Mcounteren"),
    (1, "Ibex_SpecPastWbexc_Mepc"),
    (1, "Ibex_SpecPastWbexc_Mie"),
    (1, "Ibex_SpecPastWbexc_Mscratch"),
    (1, "Ibex_SpecPastWbexc_Mseccfg"),
    (1, "Ibex_SpecPastWbexc_Mstatus"),
    (1, "Ibex_SpecPastWbexc_Mtval"),
    (1, "Ibex_SpecPastWbexc_Mtvec"),
    (1, "Ibex_SpecPastWbexc_Pc"),
    (1, "Ibex_SpecPastWbexc_Pmp_addr"),
    (1, "Ibex_SpecPastWbexc_Pmp_cfg"),
    (1, "Ibex_SpecPastWbexc_Priv"),

    (2, "Ibex_Memory_WaitRvalidMis_WaitGnt_Inv"),
    (2, "Ibex_Memory_WaitRvalidMisGntsDone_Step_Inv"),
    (2, "Ibex_Memory_WaitRvalidMisGntsDone_WaitRvalidMisGntsDone_Inv"),
    (2, "Ibex_Memory_Step_Step"),
    (2, "Ibex_Memory_StepFail_Step"),
    (2, "Ibex_Memory_IdleActive_WaitGntMis_Inv"),
    (2, "Ibex_Memory_IdleActive_WaitGnt_Inv"),
    (2, "Ibex_Memory_IdleActive_Step"),

    (3, "Ibex_Memory_End_Rev"),

    (5, "Ibex_BecameDecodeIsEmptyWbexc"),
    (5, "Ibex_BecameDecodeIsInstrStart"),
    (5, "Ibex_DivInstrNotMult"),
    (5, "Ibex_MultEndState"),

    (6, "Ibex_SpecStableStoreSndData"),
    (6, "Ibex_FetchErrRoot"),
    (6, "Ibex_FirstCycleNoGnt"),
    (6, "Ibex_PreNextPcMatch"),
    (6, "Ibex_SpecStableStore"),
    (6, "Ibex_SpecStableStoreAddr"),
    (6, "Ibex_SpecStableStoreData"),
    (6, "Ibex_LoadNotSpecWrite"),
    (6, "Ibex_NewIdFSM"),
    (6, "Ibex_SpecStableStoreSndAddr"),
    (6, "Ibex_SpecStableStoreSnd"),

    (7, "Ibex_IRQMainResMatch"),

    (8, "Ibex_SpecEnUnreach"),

    (9, "Mem_EarlyLSUCtrlMatch"),
    (9, "Mem_LoadPMPErrorWx"),
    
    (10, "Fence_FenceI_PC"),

    (21, "RegMatch_14"),
]
if len(SKIPPED_PROPS) > 0:
    print(orange(f"WARNING: Skipped properties: {' '.join([x[1] for x in SKIPPED_PROPS])}"))

HIGH_LEVEL_STRATEGY = [
    "normal", # 0
    "normal", # 1
    "normal", # 2
    # "properties", # 2
    "normal", # 3
    "normal", # 4
    "normal", # 5
    "properties", # 6
    "normal", # 7
    "normal", # 8
    "prefix", # 9
]

NO_SAVE = False

async def main():
    def preproc_name(name):
        first = name.split("$")[1][5:]
        assert first.startswith("Step")
        step, rest = first.split("_", maxsplit=1)
        step = int(step[4:])
        return step, rest

    process_runner.start_loop()

    print(white("Reading property list"))
    with open("build/noprops.aig.map") as f:
        names = [preproc_name(x[0]) for x in json.load(f)["asserts"]]
    by_step = []
    for step, name in names:
        if (step, name) in SKIPPED_PROPS:
            continue
        while step >= len(by_step):
            by_step.append([])
        by_step[step].append(name)

    async def get_strategy(step, props):
        if not NO_SAVE:
            try:
                with open(f"strategies/step{step}.json", "r") as f:
                    print(white(f"Loading strategy for step {step} from cache"))
                    return json.load(f)
            except FileNotFoundError:
                pass
            except json.JSONDecodeError as e:
                print(red(f"Error decoding step{step}.json (ignoring): {e}"))

        print(white(f"Building strategy for step {step} ({len(props)} properties)"))
        build_start = time.time()

        highlevel = "normal"
        if step < len(HIGH_LEVEL_STRATEGY):
            highlevel = HIGH_LEVEL_STRATEGY[step]

        match highlevel:
            case "normal":
                print(white("strategy: name based recursive splitting, linear fallback"))
                blocks = split_by_prefixes(props)
                strategy = await build_strategy_rec(step, blocks)
            # case "small":
            #     print(white("strategy: small initial chunk, recursive splitting"))
            #     strategy = await build_strategy(step, props, max_chunk=4)
            # case "prefix":
            #     print(white("strategy: initially split by prefix"))
            #     print(blocks)
            #     exit(1)
                # strategy = await build_strategy(step, props, max_chunk=4)
            case "properties":
                print(white("strategy: each property"))
                strategy = []
                for x in await asyncio.gather(*[build_strategy_rec(step, [prop]) for prop in props]):
                    strategy.extend(x)
            case x:
                print(red(f"ERROR: Unknown high level strategy {x}, using normal"))
                print(white("strategy: name based recursive splitting, linear fallback"))
                blocks = split_by_prefixes(props)
                strategy = await build_strategy_rec(step, blocks)
        
        build_dt = time.time() - build_start
        print(gray(json.dumps(strategy)))
        strategy = json.loads(json.dumps(strategy)) # Normalize, just in case, so that this run in is the same as the rest
        print(white(f"Constructed strategy for step {step} of {len(strategy)} proof steps in {build_dt:.3f}s"))
        if not NO_SAVE:
            try:
                os.makedirs("strategies", exist_ok=True)
                with open(f"strategies/step{step}.json", "w") as f:
                    json.dump(strategy, f)
            except Exception as e:
                print(red(f"ERROR: Could not save strategy: {e}"))
        return strategy

    for step, props in enumerate(by_step):
        if step < 19:
            print(orange(f"Skipping step {step}"))
            continue

        strategy = await get_strategy(step, props)

        if len(strategy) != 1:
            print(white(f"Running strategy for step {step} ({len(props)} properties)"))
            run_start = time.time()
            await run_strategy(strategy)
            run_dt = time.time() - run_start
            print(white(f"Ran strategy for step {step} in {run_dt:.3f}s"))
        else:
            print(white(f"Skipping proof run for step {step}, since it has just one step"))
    
    all_strategies = []
    for step, props in enumerate(by_step):
        all_strategies.extend(await get_strategy(step, props))

    print(white(f"Running strategy for everything"))
    run_start = time.time()
    await run_strategy(all_strategies)
    run_dt = time.time() - run_start
    print(white(f"Ran strategy for everything in {run_dt:.3f}s"))

asyncio.run(main())
