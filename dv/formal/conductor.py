import asyncio
import argparse
import re
import subprocess
import time
import json
import os
from math import floor
from types import CoroutineType
from typing import Any, Coroutine, TypeVar
from datetime import datetime
import re
import hashlib

# --------------------- Utilities ----------------------

oldprint = print
def print(*args):
    timestr = datetime.now().strftime('[%d/%m/%y %H:%M:%S.%f]')
    oldprint(gray(timestr), *args)
    if not "NO_LOG" in os.environ:
        with open("logfile.txt", "a") as f:
            oldprint(timestr, *[re.sub("\033\\[[0-9;]+m", "", str(x)) for x in args], file=f)
if not "NO_LOG" in os.environ:
    with open("logfile.txt", "a") as f:
        f.write("\n")

def green(s): return f"\033[32;1m{s}\033[0m"
def red(s): return f"\033[31;1m{s}\033[0m"
def white(s): return f"\033[1m{s}\033[0m"
def orange(s): return f"\033[33;1m{s}\033[0m"
def gray(s): return f"\033[90m{s}\033[0m"

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

# --------------------- Process Management ----------------------

def global_memory_free():
    with open("/proc/meminfo", "r") as f:
        c = f.read()
        for line in c.split("\n"):
            if line.startswith("MemFree:"):
                return float(line[8:-2].strip()) / (1024 * 1024)
    return 0

def pid_memory_used(pid):
    with open(f"/proc/{pid}/status", "r") as f:
        c = f.read()
        for line in c.split("\n"):
            if line.startswith("RssAnon:"):
                return float(line[8:-2].strip()) / (1024 * 1024)
    return 0

class ProcessFuture(asyncio.Future):
    def __init__(self, loop, proc):
        super().__init__(loop=loop)
        self.proc = proc

    def cancel(self, msg = None):
        self.proc.kill()
        return super().cancel(msg=msg)

class Process:
    def __init__(self, cmd, promise_quick = False, expected_memory = 0, expected_time = 0, timeout = None, debug_slow = None):
        self.cmd = cmd
        self.promise_quick = promise_quick
        self.expected_memory = expected_memory
        self.expected_time = expected_time
        self.timeout = timeout
        self.kill_ = None
        
        self.debug_slow = debug_slow
        self.debug_slow_count = 0

        self.proc = None

        self.future: asyncio.Future[tuple[int | None, float, float, str]] = ProcessFuture(asyncio.get_running_loop(), self)

        self.max_memory = 0
        self.start_time = 0

    def start(self):
        print("$", self.cmd)
        self.proc = subprocess.Popen(self.cmd, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.start_time = time.time()
        self.max_memory = 0

    def kill(self):
        self.kill_ = "kill"

    def kill_restart(self):
        self.kill_ = "restart"

    def poll(self):
        assert self.proc is not None

        dt = time.time() - self.start_time
        code = self.proc.poll()
        if code is not None and self.kill_ == None:
            print(f"Finished `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            if not self.future.cancelled():
                self.future.set_result((code, self.max_memory, dt, "OK", self.proc.stdout.read().decode(), self.proc.stderr.read().decode()))
            return True
        elif self.kill_ == "restart":
            print(gray(f"Kill (will restart) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)"))
            self.proc.kill()
            self.kill_ = None
            self.expected_memory = max(self.expected_memory, self.max_memory)
            self.expected_time = max(self.expected_time, dt)
            return True
        elif self.timeout is not None and dt > self.timeout:
            print(f"Kill `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result((None, self.max_memory, dt, "TIMEOUT", None, self.proc.stderr.read().decode()))
            return True
        elif self.kill_ == "kill":
            print(gray(f"Kill (uninterested) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)"))
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result((None, self.max_memory, dt, "UNINTERESTED", None, self.proc.stderr.read().decode()))
            return True

        self.max_memory = max(pid_memory_used(self.proc.pid), self.max_memory)

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
        self.first_start = 0

    def append(self, proc):
        # FIXME: Use a circular buffer
        self.pending.insert(0, proc)

    def start_loop(self):
        asyncio.get_running_loop().call_soon(lambda: self.poll())

    def poll(self):
        # Kill recently started processes until memory is OK, unless there is just one, then there's no point
        free = global_memory_free()
        while free < ProcessRunner.GLOBAL_MEMORY_BUFFER and len(self.running) > 1:
            last = self.running.pop()
            last.kill_restart()
            free += max(last.max_memory, 3)
            last.poll()
            self.pending.append(last)

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
print(f"Process runner will have a maximum of {ProcessRunner.MAX_RUNNING} processes, and currently sees {global_memory_free():.3f}GB free.")

process_runner = ProcessRunner()

async def shell(cmd, promise_quick = False, expected_memory = 0, timeout = None, debug_slow = None):
    proc = Process(cmd, promise_quick=promise_quick, expected_memory=expected_memory, timeout=timeout, debug_slow=debug_slow)
    process_runner.append(proc)
    return await proc.future

# ------------------------ Proof Primitives ------------------

aiger_idx = 0
async def prepare_aiger(step, props):
    global aiger_idx

    name = f"build/aiger-{aiger_idx}.aig"
    aiger_idx += 1
    assert (await shell(
        f"build/aig-manip build/all.aig select {name} build/all.ywmap {step} {' '.join(props)}",
        expected_memory=0.5
    ))[0] == 0

    return name

def proof_done(engine_config, path, step, props, results):
    code = results[0]
    mem = results[1] or 0.0
    dt = results[2] or 0.0
    if not "NO_LOG" in os.environ:
        with open("prooflog.txt", "a") as f:
            json.dump([time.time(), props, step, code, mem, dt, ROOT_HASH, engine_config], f)
            f.write("\n")
    match code:
        case 20:
            print(green(f"UNSAT: {len(props)} properties in step {step} proven in {dt:.3f}s with {mem:.3f}GB"))
            return "OK"
        case 10:
            print(red(f"=========================================================================================================================="))
            print(red(f"=========================================================================================================================="))
            print(red(f"=========================================================================================================================="))
            print(red(f"       ==================== SAT: CEX in step {step}, discovered in {dt:.3f}s with {mem:.3f}GB =================="))
            print(red(f"=========================================================================================================================="))
            print(red(f"=========================================================================================================================="))
            print(red(f"=========================================================================================================================="))
            print(f"To recover a witness run the following:")
            print(f"    {engine_config} {path} --witness | tail -n +2 > witness.aiw")
            print(f"Or the following:")
            print(f"    rIC3 -e bmc --no-preproc {path} --witness | tail -n +2 > witness.aiw")
            print(f"Then to view the trace:")
            print(f"    build/aig-manip {path} simulate build/all.ywmap build/all.vmap witness.aiw trace.vcd")
            print(f"    gtkwave trace.vcd")
            return "CEX"
        case 30:
            print(orange(f"UNDETERMINED: Failed to find a CEX or proof for {len(props)} properties in step {step} ({dt:.3f}s with {mem:.3f}GB)"))
            return "UNDETERMINED"
        case -9:
            print(red(f"KILLED by OS: Failed to prove {len(props)} properties in step {step} ({dt:.3f}s with {mem:.3f}GB)"))
            return "KILL"
        case None:
            print(red(f"TIMEOUT: Failed to prove {len(props)} properties in step {step} ({dt:.3f}s with {mem:.3f}GB)"))
            return "TIMEOUT"
        case n:
            print(red(f"Unknown Exit Code {n}: Failed to prove {len(props)} properties in step {step} ({dt:.3f}s with {mem:.3f}GB)"))
            return "UNKNOWN"

async def prove(engine_config, step, props, post="", timeout=None, expected_memory=0):
    specialised = await prepare_aiger(step, props)
    res = await shell(f"{engine_config} {specialised}{post}", timeout=timeout, expected_memory=expected_memory)
    proof_done(engine_config, specialised, step, props, res)
    return res

cex_id = 0
async def bmc(step, props, timeout=None, start=None, end=None):
    global cex_id
    res = await prove("rIC3 -e bmc --no-preproc --witness" + ("" if start is None else f" --start {start}") + ("" if end is None else f" --end {end}"), step, props, timeout=timeout)
    if res[0] == 10:
        own_id = cex_id
        cex_id += 1
        witness = res[4].split("\n", maxsplit=1)[1]
        with open(f"witness-{own_id}.aiw", "w") as f:
            f.write(witness)
        print(white(f"Written trace to witness-{own_id}.aiw"))
        await shell(f"./aig-manip/target/release/aig-manip build/all.aig simulate build/all.ywmap build/all.vmap witness-{own_id}.aiw trace-{own_id}.vcd")
        print(white(f"Produced VCD file at trace-{own_id}.vcd"))
    return res

# -------------------------- Proof Exploration -----------------------

async def explore(step, props, configs, timeout=0.0, debug_slow=None) -> asyncio.Future[None | tuple[str, tuple[int, float, float, str]]]:
    specialised = await prepare_aiger(step, props)

    async def explore_one(engine_config, idx, expected_memory):
        result = await shell(f"{engine_config} {specialised}", timeout=timeout, expected_memory=expected_memory, debug_slow=debug_slow)
        proof_done(engine_config, specialised, step, props, result)
        if result[0] in {10, 20}:
            won_race((engine_config, result))
    
    return await race([explore_one(config, idx, mem) for idx, (config, mem) in enumerate(configs)])

failures = []
async def build_strategy_rec(step, prop_tree, eager=False, difficult=False):
    def find_all(prop_tree, all_props):
        for prop in prop_tree:
            if type(prop) == str:
                all_props.append(prop)
            else:
                find_all(prop, all_props)
    all_props = []
    find_all(prop_tree, all_props)

    if difficult:
        ENGINES = [
            ("rIC3", 10),
            # ("rIC3 --no-preproc", 20),
            ("rIC3 -e kind --no-preproc", 10),
            ("rIC3 -e kind", 10)
        ]
    else:
        ENGINES = [
            ("rIC3", 10),
            # ("rIC3 --no-preproc", 20),
            ("rIC3 -e kind --no-preproc", 10),
            # ("rIC3 -e kind", 10)
        ]

    if len(all_props) == 0:
        return []

    if len(all_props) == 1:
        while True:
            res = await explore(step, all_props, timeout=1800.0 if difficult else 600.0, configs=ENGINES, debug_slow=lambda dt: print(gray(f"Still exploring step {step} property {all_props[0]} ({dt:.3f}s)")))
            if res is not None:
                print(green(f"Constructed proof for 1 property in step {step}: {all_props[0]}"))
                return [(step, all_props, res[0], res[1])]
            print(red(f"Failed to find proof for property in step {step}: {all_props[0]} - ignoring"))
            failures.append((step, all_props[0]))
            return []

    if len(prop_tree) == 1:
        return await build_strategy_rec(step, prop_tree[0], difficult=difficult)

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
            solutions = await asyncio.gather(*[build_strategy_rec(step, [child], difficult=difficult) for child in rest])
        else:
            children.append(rest)
            solutions = await asyncio.gather(*[build_strategy_rec(step, tree, difficult=difficult) for tree in children])
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

# ---------------------------------- Main ------------------------------

parser = argparse.ArgumentParser(prog="conductor.py", description="Constructs and executes proofs.")
parser.add_argument("mode", choices=["prove", "explore", "bmc", "info"], help="Proof mode. prove will run existing proofs where they exist, explore will attempt to discover new proofs, bmc will run BMC on each property individually, info dumps stats about cached proofs.")
parser.add_argument("--fresh", action="store_true", help="In explore mode, do not use already constructed proofs, always construct new proofs.")
parser.add_argument("--no-store", action="store_true", help="In explore mode, do not store constructed proof strategies.")
parser.add_argument("--by-step", action="store_true", help="In prove mode, do proofs one step at a time")
parser.add_argument("-p", "--properties", nargs="*", default=[], help="Restrict to only the properties with the given names, otherwise all properties. Especially helpful for BMC.")
parser.add_argument("--missing", action="store_true", help="Equivalent to -p <each property that is not skipped but has no proof in a step where there are some proofs>")
parser.add_argument("-s", "--start", type=int, default=0, help="First step to start at. (default: 0)")
parser.add_argument("--bmc-step", type=int, default=1, help="Step size for BMC. (default: 1)")
parser.add_argument("--bmc-start", type=int, default=4, help="Start length for BMC. (default: 4)")
parser.add_argument("--hard", action="store_true", help="In explore mode, try harder to prove properties (1hr timeout, more engines).")
parser.add_argument("--no-run", action="store_true", help="In explore mode don't run proofs again to check steps.")
args = parser.parse_args()

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

    (2, "Ibex_Memory_WaitRvalidMisGntsDone_Step_Inv"),
    (2, "Ibex_Memory_WaitRvalidMisGntsDone_WaitRvalidMisGntsDone_Inv"),
    
    (3, "Ibex_Memory_End_Rev"),

    (5, "Ibex_BecameDecodeIsEmptyWbexc"),
    (5, "Ibex_BecameDecodeIsInstrStart"),
    (5, "Ibex_DivInstrNotMult"),
    (5, "Ibex_MultEndState"),

    (6, "Ibex_MemStartFirstCycle"),
    (6, "Ibex_FirstCycleNoGnt"),
    (6, "Ibex_PreNextPcMatch"),
    (6, "Ibex_NewIdFSM"),

    # Just are provable, they just take too long
    (10, 'MType_Div_PC'),
    (10, 'MType_Rem_PC'),
    (10, 'MType_DivU_PC'),
    (10, 'MType_RemU_PC'),

    (12, 'Mem_NoMem'),

    # These are not intended to be enabled, the rest are
    (10, 'UType_Auipc_FalseCheck'),
    (10, 'UType_Lui_FalseCheck'),
    (10, 'MType_Div_Data'),
    (10, 'MType_Rem_Data'),
    (10, 'MType_Mul_Data'),
    (10, 'MType_RemU_Data'),
    (10, 'MType_MulH_Data'),
    (10, 'MType_DivU_Data'),
    (10, 'MType_MulHU_Data'),
    (10, 'MType_MulHSH_Data'),
]
if len(SKIPPED_PROPS) > 0:
    print(orange(f"WARNING: Skipped properties are {' '.join([x[1] for x in SKIPPED_PROPS])}"))

with open("build/all.aig", "rb") as f:
    ROOT_HASH = hashlib.new("sha256", f.read()).hexdigest()
print(f"build/all.aig has sha256 {ROOT_HASH}")

def load_strategy(step):
    if args.fresh:
        return None
    try:
        with open(f"strategies/step{step}.json", "r") as f:
            print(white(f"Loading strategy for step {step} from cache"))
            return json.load(f)
    except FileNotFoundError:
        pass
    except json.JSONDecodeError as e:
        print(red(f"Error decoding step{step}.json (ignoring): {e}"))
    return None

def missing_from(strategy, props):
    done_props = []
    for strategy_step in strategy:
        done_props.extend(strategy_step[1])
    return list(set(props).difference(done_props))

async def bmc_mode(props):
    if len(props) == 1:
        step, prop = props[0]
        print(white(f"Doing unbounded BMC for step on {prop} from step {step}"))
        await bmc(step, [prop], start=args.bmc_start)
        return

    if len(props) == 0:
        print(red("No properties to do BMC on!"))
        return
    i = args.bmc_start
    while True:
        for step, prop in props:
            print(white(f"Doing BMC at depth {i} on {prop} from step {step}"))
            await bmc(step, [prop], start=i, end=i)
        i += args.bmc_step

async def info_mode(by_step, by_step_skipped):
    for step, props in enumerate(by_step):
        strategy = load_strategy(step)
        if strategy is None:
            print(orange(f"No proof strategy entry for step {step}"))
            strategy = []
        accounted_for = []
        for stepi in strategy:
            print(f"Step {stepi[0]} :: {stepi[3][3]} :: {stepi[3][1]:.3f}GB/{stepi[3][2]:.3f}s :: {stepi[2]} :: {' '.join(stepi[1])}")
            accounted_for.extend(stepi[1])
        if len(by_step_skipped[step]) > 0:
            print(orange(f"Step {step} :: SKIPPED :: :: :: {' '.join(by_step_skipped[step])}"))
        unaccounted = []
        for prop in by_step[step]:
            if prop not in accounted_for:
                unaccounted.append(prop)
        if len(unaccounted) > 0:
            print(red(f"Step {step} :: UNACCOUNTED :: :: :: {' '.join(unaccounted)}"))

async def prove_mode(by_step):
    all_strategies = []
    for step, props in enumerate(by_step):
        if step < args.start:
            print(orange(f"Skipping step {step}"))
            continue
        strategy = load_strategy(step)
        if strategy is None or len(strategy) == 0:
            print(orange(f"No strategy for step {step}, skipping"))
            continue

        if args.by_step:
            print(white(f"Running strategy for step {step} ({len(props)} properties)"))
            run_start = time.time()
            await run_strategy(strategy)
            run_dt = time.time() - run_start
            print(white(f"Ran strategy for step {step} in {run_dt:.3f}s"))
        else:
            all_strategies.extend(strategy)

    if not args.by_step:
        print(white(f"Running strategy for everything"))
        run_start = time.time()
        await run_strategy(all_strategies)
        run_dt = time.time() - run_start
        print(white(f"Ran strategy in {run_dt:.3f}s"))

async def construct_strategy(step, props):
    strategy = load_strategy(step) or []
    not_done = missing_from(strategy, props)
    if len(not_done) == 0:
        return False, strategy

    print(white(f"Building strategy for step {step} ({len(not_done)}/{len(props)} properties)"))
    build_start = time.time()

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

    if args.hard:
        highlevel = "properties"
    elif step < len(HIGH_LEVEL_STRATEGY):
        highlevel = HIGH_LEVEL_STRATEGY[step]
    else:
        highlevel = "normal"

    match highlevel:
        case "normal":
            print(white("strategy: name based recursive splitting, linear fallback"))
            blocks = split_by_prefixes(not_done)
            strategy += await build_strategy_rec(step, blocks, difficult=args.hard)
        case "properties":
            print(white("strategy: each property"))
            for x in await asyncio.gather(*[build_strategy_rec(step, [prop], difficult=args.hard) for prop in not_done]):
                strategy.extend(x)
        case x:
            print(red(f"ERROR: Unknown high level strategy {x}, using normal"))
            print(white("strategy: name based recursive splitting, linear fallback"))
            blocks = split_by_prefixes(not_done)
            strategy += await build_strategy_rec(step, blocks, difficult=args.hard)

    build_dt = time.time() - build_start
    print(gray(json.dumps(strategy)))
    strategy = json.loads(json.dumps(strategy)) # Normalize, just in case, so that this run in is the same as the rest
    print(white(f"Constructed strategy for step {step} of {len(strategy)} proof steps in {build_dt:.3f}s"))
    if not args.no_store:
        try:
            os.makedirs("strategies", exist_ok=True)
            with open(f"strategies/step{step}.json", "w") as f:
                json.dump(strategy, f)
        except Exception as e:
            print(red(f"ERROR: Could not save strategy: {e}"))
    return True, strategy

async def explore_mode(by_step):
    for step, props in enumerate(by_step):
        if step < args.start:
            print(orange(f"Skipping step {step}"))
            continue

        new, strategy = await construct_strategy(step, props)
        if new:
            print(gray(f"All failures to date: {failures}"))
        
        if args.no_run:
            pass
        elif not new or len(strategy) != 1:
            print(white(f"Running strategy for step {step} ({len(props)} properties)"))
            run_start = time.time()
            await run_strategy(strategy)
            run_dt = time.time() - run_start
            print(white(f"Ran strategy for step {step} in {run_dt:.3f}s"))
        else:
            print(white(f"Skipping proof run for step {step}, since it has just one step"))         

async def main():
    def preproc_name(name):
        first = name.split("$")[1][5:]
        assert first.startswith("Step")
        step, rest = first.split("_", maxsplit=1)
        step = int(step[4:])
        return step, rest

    def group_by_step(names, max=None):
        by_step = []
        for step, name in names:
            while step >= len(by_step):
                by_step.append([])
            by_step[step].append(name)
        if max is not None:
            while max >= len(by_step):
                by_step.append([])
        return by_step

    process_runner.start_loop()

    print(white("Reading property list"))
    with open("build/all.ywmap") as f:
        names = [preproc_name(x[0]) for x in json.load(f)["asserts"]]
    max_step = max(step for step, _ in names)
    names = [(step, name) for step, name in names if not name.endswith("_Cover")]

    by_step = group_by_step(names)
    props = []
    for prop in args.properties:
        for step, name in names:
            if prop == name:
                props.append((step, prop))
                break
        else:
            print(red(f"ERROR: Property not found {prop}"))
            exit(1)
    if args.missing:
        for step, sprops in enumerate(by_step):
            strategy = load_strategy(step)
            if strategy is None:
                continue
            props.extend([(step, p) for p in missing_from(strategy, sprops)])
    elif len(props) == 0:
        props = names
    props_skipped = [(step, p) for step, p in props if (step, p) in SKIPPED_PROPS]
    props = [(step, p) for step, p in props if (step, p) not in SKIPPED_PROPS]

    if len(props) == 0 and len(props_skipped) == 0:
        print(orange("Warning: Empty property selection"))

    skipped_by_step = group_by_step(props_skipped, max_step)
    by_step = group_by_step(props, max_step)

    match args.mode:
        case "bmc":
            await bmc_mode(props)
        case "info":
            await info_mode(by_step, skipped_by_step)
        case "prove":
            await prove_mode(by_step)
        case "explore":
            await explore_mode(by_step)
        

asyncio.run(main())
