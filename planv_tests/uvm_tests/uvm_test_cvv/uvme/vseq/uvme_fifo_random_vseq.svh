// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_RANDOM_VSEQ_SVH__
`define __UVME_FIFO_RANDOM_VSEQ_SVH__

class uvme_fifo_random_vseq_c extends uvme_fifo_base_vseq_c;

    `uvm_object_utils(uvme_fifo_random_vseq_c)

    extern function new(string name="uvme_fifo_random_vseq");

    extern virtual task body();

endclass : uvme_fifo_random_vseq_c


function uvme_fifo_random_vseq_c::new(string name="uvme_fifo_random_vseq");

    super.new(name);

endfunction : new


task uvme_fifo_random_vseq_c::body();

    uvma_wr_rd_base_sqr_c#(uvma_wr_seq_item_c) wr_sqr = p_sequencer.write_sqr;
    uvma_wr_rd_base_sqr_c#(uvma_rd_seq_item_c) rd_sqr = p_sequencer.read_sqr;

    uvma_wr_random_seq_c wr_seq;
    uvma_rd_random_seq_c rd_seq;

    fork
        begin
            `uvm_info("RANDOM_VSEQ", "uvme_fifo_random_vseq_c::body Starting write sequence (100 items).", UVM_MEDIUM)
            repeat (100) begin
                wr_seq = uvma_wr_random_seq_c::type_id::create("wr_seq");
                if (!wr_seq.randomize()) begin
                    `uvm_fatal("RANDOM_VSEQ", "uvme_fifo_random_vseq_c::body::wr_seq randomize failed")
                end
                wr_seq.start(wr_sqr);
            end
        end
        begin
            `uvm_info("RANDOM_VSEQ", "uvme_fifo_random_vseq_c::body Starting read sequence (100 items).", UVM_MEDIUM)
            repeat (100) begin
                rd_seq = uvma_rd_random_seq_c::type_id::create("rd_seq");
                if (!rd_seq.randomize()) begin
                    `uvm_fatal("RANDOM_VSEQ", "uvme_fifo_random_vseq_c::body::rd_seq randomize failed")
                end
                rd_seq.start(rd_sqr);
            end
        end

    join_none

    #2000ns;
    `uvm_info("RANDOM_VSEQ", "uvme_fifo_random_vseq_c::body Finished.", UVM_MEDIUM)

endtask : body


`endif // __UVME_FIFO_RANDOM_VSEQ_SVH__
