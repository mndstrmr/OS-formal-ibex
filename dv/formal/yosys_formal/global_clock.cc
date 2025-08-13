#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct GlobalClockPass : public Pass {
	GlobalClockPass() : Pass("global_clk", "introduce a global clock to the design, lower formal cells, and all flip flops to FFs") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    global_clk [clock name]\n");
		log("\n");
		log("    Lowers $check cells to $assert, $assume, $cover, $live or $fairness, and in\n");
		log("doing so removes any clocking information. Also replaces all FF types with\n");
		log("equivalent globally clocked FFs, where again clocking information is removed\n");
		log("entirely.\n");
		log("    This pass operates on selected whole modules, of which there may only be one.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
	  if (args.size() != 2) {
	    help();
	    return;
	  }

	  if (design->selected_whole_modules().size() != 1) {
	    log_error("Only one module may be selected");
	    return;
	  }
	  auto* mod = design->selected_whole_modules()[0];

	  auto* gclk = mod->wire(args[1]);
	  if (!gclk) {
	    log_error("Could not find global clock %s", args[1].c_str());
	    return;
	  }

		log_header(design, "Executing GLOBAL_CLK pass.\n");

    SigMap sigmap(mod);
		FfInitVals initvals(&sigmap, mod);

		std::vector<RTLIL::Cell*> cells;
		for (auto* cell : mod->cells()) cells.push_back(cell);

	  for (auto* cell : cells) {
	    if (cell->type == ID($check)) {
	      RTLIL::IdString type;
	      auto flavor = cell->getParam(ID(FLAVOR)).decode_string();
	      if (flavor == "assert") type = ID($assert);
	      else if (flavor == "assume") type = ID($assume);
	      else if (flavor == "cover") type = ID($cover);
	      else if (flavor == "live") type = ID($live);
	      else if (flavor == "fair") type = ID($fair);
	      else {
	        log_error("Bad assert flavour %s", flavor.c_str());
	        log_abort();
	      }

				RTLIL::Cell* lowered = mod->addCell(NEW_ID, type);
				lowered->attributes = cell->attributes;
				lowered->setPort(ID::A, cell->getPort(ID::A));
				lowered->setPort(ID::EN, cell->getPort(ID::EN));
				mod->swap_names(cell, lowered);
				mod->remove(cell);
				continue;
	    }

	    if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

			FfData ff(&initvals, cell);

			if (ff.has_gclk) continue;
			if (!ff.has_clk) {
			  log_error("Flip-flop has no clock, but isn't gclk %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.has_srst) {
			  log_error("has_srst %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.has_arst) {
			  log_error("has_arst %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.has_sr) {
			  log_error("has_sr %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.ce_over_srst) {
			  log_error("ce_over_srst %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.is_fine) {
			  log_error("is_fine %s\n", cell->type.c_str());
			  continue;
			}
			if (ff.has_ce) {
			  log_assert(cell->type == ID($dffe));
			  bool en_polarity = cell->getParam(ID(EN_POLARITY)).as_bool();
			  RTLIL::Const width = cell->getParam(ID(WIDTH));
			  RTLIL::SigSpec d = cell->getPort(ID(D));
			  RTLIL::SigSpec q = cell->getPort(ID(Q));
			  RTLIL::SigSpec en = cell->getPort(ID(EN));
			  mod->remove(cell);
			  
			  auto* sel = mod->addWire(NEW_ID, width.as_int()); // sel = (en == aload_polarity) ? D : Q
			  auto* mux = mod->addCell(NEW_ID, ID($mux));
			  mux->setParam(ID(WIDTH), width);
			  mux->setPort(ID(A), en_polarity ? q : d);
			  mux->setPort(ID(B), en_polarity ? d : q);
			  mux->setPort(ID(S), en);
			  mux->setPort(ID(Y), sel);

			  auto* ff = mod->addCell(NEW_ID, ID($ff));
			  ff->setParam(ID(WIDTH), width);
			  ff->setPort(ID(D), sel);
			  ff->setPort(ID(Q), q);
			  continue;
			}
			if (ff.has_aload) {
			  log_assert(cell->type == ID($aldff));
			  bool aload_polarity = cell->getParam(ID(ALOAD_POLARITY)).as_bool();
			  RTLIL::Const width = cell->getParam(ID(WIDTH));

			  RTLIL::SigBit aload = cell->getPort(ID(ALOAD));
			  RTLIL::SigSpec ad = cell->getPort(ID(AD));
			  RTLIL::SigSpec d = cell->getPort(ID(D));
			  RTLIL::SigSpec q = cell->getPort(ID(Q));
			  mod->remove(cell);
			  
			  auto* sel = mod->addWire(NEW_ID, width.as_int()); // sel = (aload == aload_polarity) ? AD : D
			  auto* mux = mod->addCell(NEW_ID, ID($mux));
			  mux->setParam(ID(WIDTH), width);
			  mux->setPort(ID(A), aload_polarity ? d : ad);
			  mux->setPort(ID(B), aload_polarity ? ad : d);
			  mux->setPort(ID(S), aload);
			  mux->setPort(ID(Y), sel);

			  auto* ff = mod->addCell(NEW_ID, ID($ff));
			  ff->setParam(ID(WIDTH), width);
			  ff->setPort(ID(D), sel);
			  ff->setPort(ID(Q), q);
			  continue;
			}

		  log_assert(cell->type == ID($dff));
			cell->type = ID($ff);
		  cell->unsetPort(ID(CLK));
		  cell->unsetParam(ID(CLK_POLARITY));
	  }
	}
} ChformalPass;

PRIVATE_NAMESPACE_END

