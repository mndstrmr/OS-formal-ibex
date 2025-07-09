'''
Fixes an issue where the Sail -> SV compiler references t_Pmpcfg_ent (in sail_genlib_ibexspec.sv) before it defines it (in ibexspec.sv)
by just moving that definition.
'''

S = """
typedef struct {
    logic [7:0] bits;
} t_Pmpcfg_ent;
"""

T = """
typedef logic [127:0] sail_int;
"""

with open("build/ibexspec.sv", "r") as f:
    c = f.read()

c = c.replace(S, "")
c = c.replace("sail_return = sail_internal_pick(zz495);", "/* removed */")
c = c.replace("main_result = main(insn_bits, mode);", "wX_sail_invoke_arg_0[0] = 0; wX_sail_invoke_arg_1[0] = 0;\n        main_result = main(insn_bits, mode);")

with open("build/ibexspec.sv", "w") as f:
    f.write(c)

with open("build/sail_genlib_ibexspec.sv", "r") as f:
    c = f.read()

with open("build/sail_genlib_ibexspec.sv", "w") as f:
    f.write(S + "\n" + c)
