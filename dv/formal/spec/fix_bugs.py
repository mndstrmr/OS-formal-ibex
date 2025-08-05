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
c = c.replace("struct {", "struct packed {")
c = c.replace("sail_return = sail_internal_pick(zz498);", "/* removed */")
c = c.replace("sail_return = sail_internal_pick(zz495);", "/* removed */")
c = c.replace("        main_result = main(insn_bits, mode);", """\
        wX_sail_invoke_arg_0[0] = 0; wX_sail_invoke_arg_1[0] = 0;
        write_ram_sail_invoke_arg_0[0] = Write_plain; write_ram_sail_invoke_arg_0[1] = Write_plain;
        write_ram_sail_invoke_arg_1[0] = 0; write_ram_sail_invoke_arg_1[1] = 0;
        write_ram_sail_invoke_arg_2[0] = 0; write_ram_sail_invoke_arg_2[1] = 0;
        write_ram_sail_invoke_arg_3[0] = 0; write_ram_sail_invoke_arg_3[1] = 0;
        read_ram_sail_invoke_arg_0[0] = Read_plain; read_ram_sail_invoke_arg_0[1] = Read_plain;
        read_ram_sail_invoke_arg_1[0] = 0; read_ram_sail_invoke_arg_1[1] = 0;
        sail_reached_unreachable_loc = 0;
        main_result = main(insn_bits, mode); \
""")
c = c.replace("sail_reached_unreachable = 1;", "if (!sail_reached_unreachable) begin sail_reached_unreachable = 1; sail_reached_unreachable_loc = `__LINE__; end")
c = c.replace("module sail_ibexspec(", "module sail_ibexspec(\n    output logic sail_reached_unreachable,\n    output logic [31:0] sail_reached_unreachable_loc,")
c = c.replace("logic sail_reached_unreachable;", "")
c = c.replace("logic [31:0] sail_reached_unreachable_loc;", "")

with open("build/ibexspec.sv", "w") as f:
    f.write(c)

with open("build/sail_genlib_ibexspec.sv", "r") as f:
    c = f.read()

with open("build/sail_genlib_ibexspec.sv", "w") as f:
    f.write(S.replace("struct", "struct packed") + "\n" + c)
