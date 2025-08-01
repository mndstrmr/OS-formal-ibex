// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SPIKE_COSIM_H_
#define SPIKE_COSIM_H_

#include <stdint.h>

#include <deque>
#include <memory>
#include <string>
#include <vector>

#include "cosim.h"
#include "riscv/devices.h"
#include "riscv/log_file.h"
#include "riscv/processor.h"
#include "riscv/simif.h"

#define IBEX_MARCHID 22

class SpikeCosim : public simif_t, public Cosim {
 private:
  // A sigsegv has been observed when deleting isa_parser_t instances under
  // Xcelium on CentOS 7. The root cause is unknown so for a workaround simply
  // use a raw pointer for isa_parser that never gets deleted. This produces a
  // minor memory leak but it is of little consequence as when SpikeCosim is
  // being deleted it is the end of simulation and the process will be
  // terminated shortly anyway.
#ifdef COSIM_SIGSEGV_WORKAROUND
  isa_parser_t *isa_parser;
#else
  std::unique_ptr<isa_parser_t> isa_parser;
#endif
  std::unique_ptr<processor_t> processor;
  std::unique_ptr<log_file_t> log;
  bus_t bus;
  std::vector<std::unique_ptr<mem_t>> mems;
  std::vector<std::string> errors;
  bool nmi_mode;

  typedef struct {
    uint8_t mpp;
    bool mpie;
    uint32_t epc;
    uint32_t cause;
  } mstack_t;

  mstack_t mstack;

  void fixup_csr(int csr_num, uint32_t csr_val);

  struct PendingMemAccess {
    DSideAccessInfo dut_access_info;
    uint32_t be_spike;
  };

  std::vector<PendingMemAccess> pending_dside_accesses;

  bool pending_iside_error;
  uint32_t pending_iside_err_addr;

  typedef enum {
    kCheckMemOk,           // Checks passed and access succeeded in RTL
    kCheckMemCheckFailed,  // Checks failed
    kCheckMemBusError  // Checks passed, but access generated bus error in RTL
  } check_mem_result_e;

  check_mem_result_e check_mem_access(bool store, uint32_t addr, size_t len,
                                      const uint8_t *bytes);

  bool pc_is_mret(uint32_t pc);
  bool pc_is_load(uint32_t pc, uint32_t &rd_out);

  bool pc_is_debug_ebreak(uint32_t pc);
  bool check_debug_ebreak(uint32_t write_reg, uint32_t pc, bool sync_trap);

  bool check_gpr_write(const commit_log_reg_t::value_type &reg_change,
                       uint32_t write_reg, uint32_t write_reg_data);

  bool check_suppress_reg_write(uint32_t write_reg, uint32_t pc,
                                uint32_t &suppressed_write_reg);

  void on_csr_write(const commit_log_reg_t::value_type &reg_change);

  void leave_nmi_mode();

  bool change_cpuctrlsts_sync_exc_seen(bool flag);
  void set_cpuctrlsts_double_fault_seen();
  void handle_cpuctrl_exception_entry();

  void initial_proc_setup(uint32_t start_pc, uint32_t start_mtvec,
                          uint32_t mhpm_counter_num);

  void early_interrupt_handle();

  void misaligned_pmp_fixup();

  unsigned int insn_cnt;

 public:
  SpikeCosim(const std::string &isa_string, uint32_t start_pc,
             uint32_t start_mtvec, const std::string &trace_log_path,
             bool secure_ibex, bool icache_en, uint32_t pmp_num_regions,
             uint32_t pmp_granularity, uint32_t mhpm_counter_num);

  // simif_t implementation
  virtual char *addr_to_mem(reg_t addr) override;
  virtual bool mmio_load(reg_t addr, size_t len, uint8_t *bytes) override;
  virtual bool mmio_store(reg_t addr, size_t len,
                          const uint8_t *bytes) override;
  virtual void proc_reset(unsigned id) override;
  virtual const char *get_symbol(uint64_t addr) override;

  // Cosim implementation
  void add_memory(uint32_t base_addr, size_t size) override;
  bool backdoor_write_mem(uint32_t addr, size_t len,
                          const uint8_t *data_in) override;
  bool backdoor_read_mem(uint32_t addr, size_t len, uint8_t *data_out) override;
  bool step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc,
            bool sync_trap, bool suppress_reg_write) override;

  bool check_retired_instr(uint32_t write_reg, uint32_t write_reg_data,
                           uint32_t dut_pc, bool suppress_reg_write);
  bool check_sync_trap(uint32_t write_reg, uint32_t pc,
                       uint32_t initial_spike_pc);
  void set_mip(uint32_t pre_mip, uint32_t post_mip) override;
  void set_nmi(bool nmi) override;
  void set_nmi_int(bool nmi_int) override;
  void set_debug_req(bool debug_req) override;
  void set_mcycle(uint64_t mcycle) override;
  void set_csr(const int csr_num, const uint32_t new_val) override;
  void set_ic_scr_key_valid(bool valid) override;
  void notify_dside_access(const DSideAccessInfo &access_info) override;
  // The spike co-simulator assumes iside and dside accesses within a step are
  // disjoint. If both access the same address within a step memory faults may
  // be incorrectly cause on one rather than the other or the access checking
  // will break.
  // TODO: Work on spike changes to remove this restriction
  void set_iside_error(uint32_t addr) override;
  const std::vector<std::string> &get_errors() override;
  void clear_errors() override;
  unsigned int get_insn_cnt() override;
};

#endif  // SPIKE_COSIM_H_
