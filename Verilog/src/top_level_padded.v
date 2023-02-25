`include "/research/ece/lnis-teaching/Designkits/tsmc180nm/full_custom_lib/verilog/padlib_tsmc180.v"

module top_level_padded(
    input clock, fast_clk, reset,
    input cpu_serial_request_0, cpu_serial_request_1,
    input cpu_serial_request_ready_0, cpu_serial_request_ready_1,
    
    input memory_serial_response_0, memory_serial_response_1, 
    input memory_serial_response_ready_0, memory_serial_response_ready_1,

    output data_out_serial_0, data_out_serial_1,
    output data_out_serial_ready_0, data_out_serial_ready_1,

    output memory_request_serial_0, memory_request_serial_1,
    output memory_request_serial_ready_0, memory_request_serial_ready_1 
);
    pad_in pad_in0(.pad(clock), .DataIn(clock_pad));
    pad_in pad_in1(.pad(fast_clk), .DataIn(fast_clk_pad));
    pad_in pad_in2(.pad(reset), .DataIn(reset_pad));
    pad_in pad_in3(.pad(cpu_serial_request_0), .DataIn(cpu_serial_request_0_pad));
    pad_in pad_in4(.pad(cpu_serial_request_1), .DataIn(cpu_serial_request_1_pad));
    pad_in pad_in5(.pad(cpu_serial_request_ready_0), .DataIn(cpu_serial_request_ready_0_pad));
    pad_in pad_in6(.pad(cpu_serial_request_ready_1), .DataIn(cpu_serial_request_ready_1_pad));

    pad_in pad_in7(.pad(memory_serial_response_0), .DataIn(memory_serial_response_0_pad));
    pad_in pad_in8(.pad(memory_serial_response_1), .DataIn(memory_serial_response_1_pad));
    pad_in pad_in9(.pad(memory_serial_response_ready_0), .DataIn(memory_serial_response_ready_0_pad));
    pad_in pad_in10(.pad(memory_serial_response_ready_1), .DataIn(memory_serial_response_ready_1_pad));

    pad_out pad_out0(.pad(data_out_serial_0), .DataOut(data_out_serial_0_pad));
    pad_out pad_out1(.pad(data_out_serial_1), .DataOut(data_out_serial_1_pad));
    pad_out pad_out2(.pad(data_out_serial_ready_0), .DataOut(data_out_serial_ready_0_pad));
    pad_out pad_out3(.pad(data_out_serial_ready_1), .DataOut(data_out_serial_ready_1_pad));

    pad_out pad_out4(.pad(memory_request_serial_0), .DataOut(memory_request_serial_0_pad));
    pad_out pad_out5(.pad(memory_request_serial_1), .DataOut(memory_request_serial_1_pad));
    pad_out pad_out6(.pad(memory_request_serial_ready_0), .DataOut(memory_request_serial_ready_0_pad));
    pad_out pad_out7(.pad(memory_request_serial_ready_1), .DataOut(memory_request_serial_ready_1_pad));

    pad_corner corner0();
    pad_corner corner1();
    pad_corner corner2();
    pad_corner corner3();

    pad_vdd pad_vdd0();
    pad_gnd pad_gnd0();
    
    top_level top(clock_pad, fast_clk_pad, reset_pad, 
    cpu_serial_request_0_pad, cpu_serial_request_1_pad,
    cpu_serial_request_ready_0_pad, cpu_serial_request_ready_1_pad,
    memory_serial_response_0_pad, memory_serial_response_1_pad,
    memory_serial_response_ready_0_pad, memory_serial_response_ready_1_pad, 
    data_out_serial_0_pad, data_out_serial_1_pad,
    data_out_serial_ready_0_pad, data_out_serial_ready_1_pad,
    memory_request_serial_0_pad, memory_request_serial_1_pad, 
    memory_request_serial_ready_0_pad, memory_request_serial_ready_1_pad);

endmodule