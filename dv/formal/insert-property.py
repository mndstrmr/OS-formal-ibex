import inspect
import tqdm
import random
import subprocess
import threading
import json
import os
import sys
import time
from types import LambdaType

KEY_VALUE_LOC = "key_value.json"

def copy_into(obj1, obj2):
    for k in obj1:
        if k in obj2 and type(obj1[k]) == dict and type(obj2[k]) == dict:
            copy_into(obj1[k], obj2[k])
        else:
            obj2[k] = obj1[k]

def update_config(new):
    try:
        with open(KEY_VALUE_LOC, "r+") as f:
            obj = json.load(f)
            copy_into(new, obj)
            f.seek(0)
            f.truncate()
            json.dump(obj, f)
    except FileNotFoundError:
        with open(KEY_VALUE_LOC, "w") as f:
            json.dump(new, f)

def get_config(path):
    try:
        with open(KEY_VALUE_LOC, "r") as f:
            obj = json.load(f)
            for step in path.split("/"):
                if step not in obj:
                    return None
                obj = obj[step]
            return obj
    except FileNotFoundError:
        return None

'''Measured in GB'''
def global_mem_free():
    with open("/proc/meminfo") as f:
        for line in f.read().split("\n"):
            if line.startswith("MemFree:"):
                assert line.endswith("kB")
                line = line[8:-2].strip()
                return int(line) / (1024*1024)
        assert False

def pid_max_memory(pid):
    with open(f"/proc/{pid}/status") as f:
        for line in f.read().split("\n"):
            if line.startswith("RssAnon:"):
                assert line.endswith("kB")
                line = line[8:-2].strip()
                return int(line) / (1024*1024)
        return None

def task(f):
    def inner(*args):
        now = time.time()
        ret = f(*args)
        dt = time.time() - now
        return ret

def deps(depfiles, dstfiles):
    def inner1(f):
        def inner2(*args):
            dsts = dstfiles()
            if len(dsts) == 0:
                f(*args)
                return True
            
            earliest_change = 0
            for file in dstfiles(*args):
                if not os.path.exists(file):
                    f(*args)
                    return True
                t = os.path.getmtime(file)
                earliest_change = t if earliest_change == 0 else min(earliest_change, t)

            for file in depfiles(*args):
                if os.path.getmtime(file) > earliest_change:
                    f(*args)
                    return True
            return False
        return inner2
    return inner1

'''Panics if status_ok is not-none and doesn't match the return code, otherwise returns code and max_memory'''
def shell(cmd, status_ok: None | int = 0, kill = None):
    print("$", cmd)
    if not DRY:
        now = time.time()
        proc = subprocess.Popen(cmd, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        # code = proc.wait()
        pid = proc.pid

        max_memory = 0.0
        while True:
            try:
                proc.wait(2)
                break
            except subprocess.TimeoutExpired:
                curr = pid_max_memory(pid)
                if curr is None:
                    continue
                max_memory = max(max_memory, curr)
                if kill is not None and kill(pid, time.time() - now, max_memory):
                    proc.kill()
        code = proc.returncode
        if status_ok is None or code == status_ok:
            return code, max_memory
        print(f"Exitted with status {code}, aborting.")
        exit(1)
    return None, None

def get_process_name(chop=0):
    stack = inspect.stack()[1 + chop:-1]
    return ".".join(ent.function for ent in stack)

class Yosys:
    MAGIC_PHRASE = b"COMMAND FINISHED (magic from " + __file__.encode() + b")"
    
    def __init__(self):
        self.proc = subprocess.Popen(["yosys", "-Q"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=None if VERBOSE else subprocess.DEVNULL)

    def _run_to_completion(self, cmd: str, echo: bool):
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        self.proc.stdin.write(cmd.encode() + b"\n")
        self.proc.stdin.flush()
        self.proc.stdin.write(b"# " + Yosys.MAGIC_PHRASE + b"\n")
        self.proc.stdin.flush()

        out = b""

        while True:
            line = self.proc.stdout.readline()
            if line.endswith(b"# " + Yosys.MAGIC_PHRASE + b"\n"):
                break
            if not line.startswith(b"yosys>") and not line.startswith(b"yosys*>") and line != b"\n" and echo:
                sys.stdout.buffer.write(line)
                sys.stdout.buffer.flush()
            out += line

        return b"\n".join(out.strip().split(b"\n")[1:])
    
    def run(self, cmd: str):
        self._run_to_completion(cmd, VERBOSE or cmd == "stat")
        stat = self._run_to_completion("stat -json", False)
        stat = json.loads(stat)
        return stat

    def finish(self):
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        self.proc.stdin.close()
        line = self.proc.stdout.read()
        sys.stdout.buffer.write(line)
        sys.stdout.buffer.flush()
        self.proc.wait()

def yosys(cmds, ys=None):
    name = get_process_name(1)

    if DRY:
        for (c, cmd) in enumerate(cmds):
            last_time = get_config(f"steps/{name}.{c}")
            # if last_time != None:
            #     print(cmd, f" # (previously took {round(last_time, 3)}s)")
            # else:
            print(cmd)
        return
    
    ys = Yosys()
    for (c, cmd) in enumerate(cmds):
        last_time = get_config(f"steps/{name}.{c}")
        if last_time != None:
            print("yosys>", cmd, f" # (previously took {round(last_time, 3)}s)")
        else:
            print("yosys>", cmd)

        start = time.time()
        stat = ys.run(cmd)
        end = time.time()

        cmdname = cmd.split(" ")[0]
        if 'design' in stat:
            stat_str = f" ({stat['design']['num_wires']} wires, {stat['design']['num_cells']} cells)"
        else:
            stat_str = ""
        print(f"Completed {cmdname} ({name}.{c}) command in {round(end - start, 3)}s{stat_str}")

        update_config({ "steps": { f"{name}.{c}": end - start } })
    return ys.finish()

DEV = os.getenv("DEV") == "1"
VERBOSE = os.getenv("VERBOSE") == "1"
DRY = os.getenv("DRY") == "1"

AIG_MANIP = "aig-manip/target/release/aig-manip"
NOPROPS = "build/noprops.aig"
PROPLIST = "build/proplist.txt"

REDO_STEPS = list(range(1, 9))
SKIPPED = '''
Ibex_SpecPastReg
Ibex_SpecPastWbexc_Priv
Ibex_SpecPastWbexc_Mstatus
Ibex_SpecPastWbexc_Mie
Ibex_SpecPastWbexc_Mcause
Ibex_SpecPastWbexc_Mtval
Ibex_SpecPastWbexc_Mtvec
Ibex_SpecPastWbexc_Mscratch
Ibex_SpecPastWbexc_Mepc
Ibex_SpecPastWbexc_Mcounteren
Ibex_SpecPastWbexc_Pmp_cfg
Ibex_SpecPastWbexc_Pmp_addr
Ibex_SpecPastWbexc_Mseccfg
Ibex_SpecPastWbexc_Pc
'''.strip().split("\n")

def build_prop(base, step, props, dst):
    shell(f"{AIG_MANIP} {base} {base}.map {step} {dst} {' '.join(props)}")

with open(PROPLIST, "r") as f:
    proplist = []
    step = -1
    for line in f.readlines():
        if line.startswith("  "):
            proplist.append((step, line.strip()))
        else:
            step = int(line.strip())
    steps = step + 1

def explore(name, build, force=False, timeout=None):
    results = get_config(f"props/{name}/explore")
    if results is None or force: results = []
    first_dt = None
    for result in results:
        if first_dt is None or result["time"] < first_dt:
            first_dt = result["time"]

    property_is_false = False

    def early_kill(pid, dt, mem):
        return property_is_false or (first_dt is not None and dt > first_dt + 5) or (timeout is not None and dt > timeout)

    def explore_cmd(cmd):
        nonlocal first_dt, property_is_false

        print(f"\033[1mStarting proof of property {name}\033[0m")
        start = time.time()
        code, max_memory = shell(f"{cmd} build/{name}.aig", status_ok=None, kill = early_kill)
        assert max_memory is not None
        end = time.time()
        dt = end - start
        if code == 20:
            if first_dt == None:
                first_dt = dt
            print(f"\033[32;1mProved property {name}, took {round(dt, 4)}s, {round(max_memory, 4)}GB: `{cmd}`\033[0m")
        elif code == -9:
            print(f"\033[31;1mProof process killed (-9) for {name}, either OOM ({round(max_memory, 4)}GB) or timed out ({round(dt, 4)}s)\033[0m")           
        else:
            print(f"\033[31;1mFailed to prove property (code {code}) {name} ({round(dt, 4)}s)\033[0m")
            property_is_false = True

        if not property_is_false:
            results.append({
                "cmd": cmd,
                "time": dt,
                "mem": max_memory,
                "code": code,
            })

    cmds = [
        "rIC3",
        "rIC3 --no-preproc",
        "rIC3 -e kind",
        "rIC3 -e kind --no-preproc",
    ]

    procs = []
    built = False
    for cmd in cmds:
        skip = False
        for result in results:
            if result["cmd"] == cmd:
                skip = True
                break
        if skip:
            print("skipping", cmd)
            continue
        if not built:
            built = True
            build()
        proc = threading.Thread(target=explore_cmd, args=[cmd])
        proc.start()
        procs.append(proc)
    for proc in procs:
        proc.join()
    update_config({ "props": { name: { "explore": results } } })
    return results

if DRY:
    exit()

for step, prop in tqdm.tqdm(proplist):
    fullprop = f"Step{step}_{prop}"
    if prop in SKIPPED:
        print(f"\033[33;1mSkipping {fullprop}\033[0m")
        continue
    print(f"\033[1mDoing exploration for property {fullprop} (this will be run just once for this property, to determine which configurations work best)\033[0m")
    explore(fullprop, lambda: build_prop(NOPROPS, step, [prop], f"build/{fullprop}.aig"), force=step in REDO_STEPS)
    results = get_config(f"props/{fullprop}/explore")
    assert results is not None
    fastest = None
    smallest = None
    for (c, cmd) in enumerate(results):
        if cmd["code"] == -9:
            continue
        if fastest is None or cmd["time"] < results[fastest]["time"]:
            fastest = c
        if smallest is None or cmd["mem"] < results[smallest]["mem"]:
            smallest = c
    if fastest is None and smallest is None:
        print(f"\033[1mFinished exploration for property {fullprop}, no proof found\033[0m")
    else:
        assert fastest is not None and smallest is not None
        print(f"\033[1mFinished exploration for property {fullprop}, fastest is \"{results[fastest]['cmd']}\", smallest is \"{results[smallest]['cmd']}\"\033[0m")

for step in range(steps):
    sum_time = 0
    props = get_config("props")
    assert props is not None
    for prop in props:
        if not prop.startswith(f"Step{step}_"):
            continue
        fastest = 99999
        for cmd in props[prop]["explore"]:
            if cmd["code"] == 20 and cmd["time"] < fastest:
                fastest = cmd["time"]
        sum_time += fastest
    
    print(f"\033[1mDoing exploration for step {step} (timeout after {round(sum_time / 8, 4)}s) (this will be run just once for this proof step, to determine which configurations work best and if this is better than doing everything individually)\033[0m")
    explore(f"Step{step}", lambda: build_prop(NOPROPS, step, [], f"build/Step{step}.aig"), force=step in REDO_STEPS, timeout=sum_time / 8)
    results = get_config(f"props/Step{step}/explore")
    assert results is not None
    fastest = None
    smallest = None
    for (c, cmd) in enumerate(results):
        if cmd["code"] == -9:
            continue
        if fastest is None or cmd["time"] < results[fastest]["time"]:
            fastest = c
        if smallest is None or cmd["mem"] < results[smallest]["mem"]:
            smallest = c
    if fastest is None and smallest is None:
        print(f"\033[1mFinished exploration for step {step} (no faster proof found)\033[0m")
    else:
        print(f"\033[1mFinished exploration for step {step}, fastest is \"{results[fastest]['cmd']}\", smallest is \"{results[smallest]['cmd']}\"\033[0m")

tasks = []
done_via_step = set()
for step in range(steps):
    results = get_config(f"props/Step{step}/explore")
    assert results is not None
    fastest = None
    for r, res in enumerate(results):
        if res["code"] != -9 and (fastest is None or res["time"] < results[fastest]["time"]):
            fastest = r
    if fastest is not None:
        tasks.append(("step", f"Step{step}", results[fastest]))
        done_via_step.add(step)

for (step, prop) in proplist:
    if step in done_via_step:
        continue
    results = get_config(f"props/Step{step}_{prop}/explore")
    assert results is not None
    fastest = None
    for r, res in enumerate(results):
        if res["code"] != -9 and (fastest is None or res["time"] < results[fastest]["time"]):
            fastest = r
    if fastest is None:
        print(f"\033[31;1mNo proof found for property Step{step}_{prop} - skipping\033[0m")
        # exit(1)
    else:
        tasks.append(("property", f"Step{step}_{prop}", results[fastest]))

# Start longer processes first so they can run in the background
tasks.sort(key=lambda x: x[2]["time"], reverse=True)

expected_mem = 0
cpus = 0
def do_task(task):
    global expected_mem, cpus
    
    print(f"\033[1mStarting proof of {task[0]} {task[1]}\033[0m")
    start = time.time()
    code, max_memory = shell(f"{task[2]['cmd']} build/{task[1]}.aig", status_ok=None)
    dt = time.time() - start
    if code == 20:
        print(f"\033[32;1mProved {task[0]} {task[1]}, took {round(dt, 4)}s (predicted {round(task[2]['time'], 4)}s), {round(max_memory, 4)}GB (predicted {round(task[2]['mem'], 4)}GB)\033[0m")
    elif code == -9:
        print(f"\033[31;1mProof process killed (-9) for {task[0]} {task[1]}, either OOM ({round(max_memory, 4)}GB) or timed out ({round(dt, 4)}s)\033[0m")
    else:
        print(f"\033[31;1mFailed to prove {task[0]} {task[1]} (code {code}) ({round(dt, 4)}s)\033[0m")
    expected_mem -= task[2]["mem"]
    cpus -= 1

start = time.time()
threads = []
MAX_MEM = 50
for task in tasks:
    while max(global_mem_free(), MAX_MEM - expected_mem) < task[2]["mem"] * 1.2 or cpus >= 15:
        time.sleep(1)
    thread = threading.Thread(target=do_task, args=[task])
    thread.start()
    threads.append(thread)
    expected_mem += task[2]["mem"]
    cpus += 1

for thread in threads:
    thread.join()

end = time.time()
print(f"\033[1mAll tasks completed in {round(end - start, 4)}s\033[0m")

# build_prop(NOPROPS, step, [prop], f"build/{fullprop}.aig")

# build_prop(NOPROPS_IL, ["Step0"], ["Step1"], [PROP], f"build/{PROP}.aig")
# build_prop(NOPROPS, ["Step0"], ["Step1"], [PROP], f"build/{PROP}.aig")

