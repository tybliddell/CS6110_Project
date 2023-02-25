module top_level(
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
    wire [24:0] cpu_request_0, cpu_request_1;
    wire cpu_request_ready_0, cpu_request_ready_1;
    wire [7:0] data_out_0, data_out_1;
    wire data_out_ready_0, data_out_ready_1;
    wire [15:0] invalidate_address_0, invalidate_address_1;
    wire [15:0] memory_response_0, memory_response_1;
    wire memory_response_ready_0, memory_response_ready_1;
    wire [24:0] memory_request_0, memory_request_1;
    wire memory_request_ready_0, memory_request_ready_1;

    input_collector #(.OUTPUT_WIDTH(25)) cpu_0_collector(.serial_in(cpu_serial_request_0), .fast_clk(fast_clk), .ready(cpu_serial_request_ready_0), .reset(reset), .data(cpu_request_0), .data_ready(cpu_request_ready_0));
    input_collector #(.OUTPUT_WIDTH(25)) cpu_1_collector(.serial_in(cpu_serial_request_1), .fast_clk(fast_clk), .ready(cpu_serial_request_ready_1), .reset(reset), .data(cpu_request_1), .data_ready(cpu_request_ready_1));

    input_collector #(.OUTPUT_WIDTH(16)) mem_0_collector(.serial_in(memory_serial_response_0), .fast_clk(fast_clk), .ready(memory_serial_response_ready_0), .reset(reset), .data(memory_response_0), .data_ready(memory_response_ready_0));
    input_collector #(.OUTPUT_WIDTH(16)) mem_1_collector(.serial_in(memory_serial_response_1), .fast_clk(fast_clk), .ready(memory_serial_response_ready_1), .reset(reset), .data(memory_response_1), .data_ready(memory_response_ready_1));

    output_emitter #(.INPUT_WIDTH(8)) cpu_0_emitter (.data(data_out_0), .fast_clk(fast_clk), .start(data_out_ready_0), .reset(reset), .serial_out(data_out_serial_0), .serial_done(data_out_serial_ready_0));
    output_emitter #(.INPUT_WIDTH(8)) cpu_1_emitter (.data(data_out_1), .fast_clk(fast_clk), .start(data_out_ready_1), .reset(reset), .serial_out(data_out_serial_1), .serial_done(data_out_serial_ready_1));
    
    output_emitter #(.INPUT_WIDTH(25)) mem_0_emitter(.data(memory_request_0), .fast_clk(fast_clk), .start(memory_request_ready_0), .reset(reset), .serial_out(memory_request_serial_0), .serial_done(memory_request_serial_ready_0));
    output_emitter#(.INPUT_WIDTH(25)) mem_1_emitter(.data(memory_request_1), .fast_clk(fast_clk), .start(memory_request_ready_1), .reset(reset), .serial_out(memory_request_serial_1), .serial_done(memory_request_serial_ready_1));

    cache cache_0(.cpu_request(cpu_request_0), .cpu_request_ready(cpu_request_ready_0), .clock(clock), .reset(reset),
    .invalidate_address(invalidate_address_0), .memory_response(memory_response_0), .memory_response_ready(memory_response_ready_0),
    .memory_request(memory_request_0), .memory_request_ready(memory_request_ready_0), .data_out(data_out_0), .data_out_ready(data_out_ready_0));
    cache cache_1(.cpu_request(cpu_request_1), .cpu_request_ready(cpu_request_ready_1), .clock(clock), .reset(reset),
    .invalidate_address(invalidate_address_1), .memory_response(memory_response_1), .memory_response_ready(memory_response_ready_1),
    .memory_request(memory_request_1), .memory_request_ready(memory_request_ready_1), .data_out(data_out_1), .data_out_ready(data_out_ready_1));
    
    cache_coherenter coherenter(.cache_change_0(memory_request_0), .cache_change_1(memory_request_1), .cache_invalidate_0(invalidate_address_0), .cache_invalidate_1(invalidate_address_1),
                                .clock(clock), .reset(reset));

endmodule