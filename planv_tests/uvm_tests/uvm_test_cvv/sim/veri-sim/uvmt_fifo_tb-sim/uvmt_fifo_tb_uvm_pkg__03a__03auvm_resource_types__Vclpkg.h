// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_TYPES__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_TYPES__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg.h"


class uvmt_fifo_tb__Syms;
struct uvmt_fifo_tb_access_t__struct__0 {
    QData/*63:0*/ __PVT__read_time;
    QData/*63:0*/ __PVT__write_time;
    IData/*31:0*/ __PVT__read_count;
    IData/*31:0*/ __PVT__write_count;

    bool operator==(const uvmt_fifo_tb_access_t__struct__0& rhs) const {
        return __PVT__read_time == rhs.__PVT__read_time
            && __PVT__write_time == rhs.__PVT__write_time
            && __PVT__read_count == rhs.__PVT__read_count
            && __PVT__write_count == rhs.__PVT__write_count;
    }
    bool operator!=(const uvmt_fifo_tb_access_t__struct__0& rhs) const {
        return !(*this == rhs);
    }

    bool operator<(const uvmt_fifo_tb_access_t__struct__0& rhs) const {
        return std::tie(__PVT__read_time, __PVT__write_time, __PVT__read_count, __PVT__write_count)
            <  std::tie(rhs.__PVT__read_time, rhs.__PVT__write_time, rhs.__PVT__read_count, rhs.__PVT__write_count);
    }
};
template <>
struct VlIsCustomStruct<uvmt_fifo_tb_access_t__struct__0> : public std::true_type {};

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

std::string VL_TO_STRING(const uvmt_fifo_tb_access_t__struct__0& obj);

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types : public virtual VlClass {
  public:
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types>& obj);

#endif  // guard
