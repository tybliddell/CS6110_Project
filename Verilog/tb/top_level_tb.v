`timescale 100 ns/10 ps
`define SIM_MEMORY_BYTE(address) sim_memory[address * 8+:8] 
`define SIM_MEM_SIZE (65_536*8) - 1

module top_level_tb;
    localparam period = 100;
    localparam half_period = period / 2;
    localparam fast_period = period / 50;
    localparam fast_half_period = fast_period / 2;

    reg[`SIM_MEM_SIZE:0] sim_memory;
    integer i, random_cpu;
    reg [15:0] test_addy;
    reg [7:0] test_data;

    reg clock, fast_clk, reset;
    reg [24:0] cpu_request_0, cpu_request_1;
    reg cpu_request_ready_0, cpu_request_ready_1;
    reg [15:0] memory_response_0, memory_response_1;
    reg memory_response_ready_0, memory_response_ready_1;

    wire cpu_request_serial_0, cpu_request_serial_1;
    wire cpu_request_serial_ready_0, cpu_request_serial_ready_1;

    wire memory_response_serial_0, memory_response_serial_1;
    wire memory_response_serial_ready_0, memory_response_serial_ready_1;

    wire data_out_serial_0, data_out_serial_1;
    wire data_out_serial_ready_0, data_out_serial_ready_1;
    wire [7:0] data_out_0, data_out_1;
    wire data_out_ready_0, data_out_ready_1;

    wire memory_request_serial_0, memory_request_serial_1;
    wire memory_request_serial_ready_0, memory_request_serial_ready_1;
    wire [24:0] memory_request_0, memory_request_1;
    wire memory_request_ready_0, memory_request_ready_1;

    output_emitter #(.INPUT_WIDTH(25)) serialize_cpu_request_0(.data(cpu_request_0), .fast_clk(fast_clk), .start(cpu_request_ready_0), .reset(reset), .serial_out(cpu_request_serial_0), .serial_done(cpu_request_serial_ready_0));
    output_emitter #(.INPUT_WIDTH(25)) serialize_cpu_request_1(.data(cpu_request_1), .fast_clk(fast_clk), .start(cpu_request_ready_1), .reset(reset), .serial_out(cpu_request_serial_1), .serial_done(cpu_request_serial_ready_1));
    output_emitter #(.INPUT_WIDTH(16)) serialize_memory_response_0(.data(memory_response_0), .fast_clk(fast_clk), .start(memory_response_ready_0), .reset(reset), .serial_out(memory_response_serial_0), .serial_done(memory_response_serial_ready_0));
    output_emitter #(.INPUT_WIDTH(16)) serialize_memory_response_1(.data(memory_response_1), .fast_clk(fast_clk), .start(memory_response_ready_1), .reset(reset), .serial_out(memory_response_serial_1), .serial_done(memory_response_serial_ready_1));
    
    input_collector #(.OUTPUT_WIDTH(8)) collect_data_out_0(.serial_in(data_out_serial_0), .fast_clk(fast_clk), .ready(data_out_serial_ready_0), .reset(reset), .data(data_out_0), .data_ready(data_out_ready_0));
    input_collector #(.OUTPUT_WIDTH(8)) collect_data_out_1(.serial_in(data_out_serial_1), .fast_clk(fast_clk), .ready(data_out_serial_ready_1), .reset(reset), .data(data_out_1), .data_ready(data_out_ready_1));
    input_collector #(.OUTPUT_WIDTH(25)) collect_memory_request_0(.serial_in(memory_request_serial_0), .fast_clk(fast_clk), .ready(memory_request_serial_ready_0), .reset(reset), .data(memory_request_0), .data_ready(memory_request_ready_0));
    input_collector #(.OUTPUT_WIDTH(25)) collect_memory_request_1(.serial_in(memory_request_serial_1), .fast_clk(fast_clk), .ready(memory_request_serial_ready_1), .reset(reset), .data(memory_request_1), .data_ready(memory_request_ready_1));

    top_level uut(.clock(clock), .fast_clk(fast_clk), .reset(reset), .cpu_serial_request_0(cpu_request_serial_0), .cpu_serial_request_1(cpu_request_serial_1), 
    .cpu_serial_request_ready_0(cpu_request_serial_ready_0), .cpu_serial_request_ready_1(cpu_request_serial_ready_1), .memory_serial_response_0(memory_response_serial_0), .memory_serial_response_1(memory_response_serial_1),
    .memory_serial_response_ready_0(memory_response_serial_ready_0), .memory_serial_response_ready_1(memory_response_serial_ready_1), 
    .data_out_serial_0(data_out_serial_0), .data_out_serial_1(data_out_serial_1), .data_out_serial_ready_0(data_out_serial_ready_0), .data_out_serial_ready_1(data_out_serial_ready_1),
    .memory_request_serial_0(memory_request_serial_0), .memory_request_serial_1(memory_request_serial_1), .memory_request_serial_ready_0(memory_request_serial_ready_0), .memory_request_serial_ready_1(memory_request_serial_ready_1));

    always #half_period begin
        clock = ~clock;
    end
    always #fast_half_period begin
        fast_clk = ~fast_clk;
    end

    /* reset the cache to all invalid, inputs to 0, and sim_memory to 0 */
    task reset_cache;
        begin
            clock = 1'b0;
            fast_clk = 1'b0;
            reset = 1'b1;
            cpu_request_ready_0 = 1'd0;
            memory_response_ready_0 = 1'd0;
            cpu_request_0 = 25'd0;
            memory_response_0 = 16'd0;
            cpu_request_ready_1 = 1'd0;
            memory_response_ready_1 = 1'd0;
            cpu_request_1 = 25'd0;
            memory_response_1 = 16'd0;
            sim_memory = 65_536'd0;
            #period;
            reset = 1'd0;
            #period;
            reset = 1'd1;
            #period;
            $display("[status] cache reset");
        end
    endtask

    /* Write data to address, check value against memory */
    task write_value_and_check;
        input [7:0] data;
        input [15:0] address;
        input cpu;
        begin
            #period;
            if(cpu == 0) begin
                cpu_request_0 = { 1'd1, data, address };
                cpu_request_ready_0 = 1'd1;
                while(data_out_ready_0 == 1'd0 && memory_request_ready_0 == 1'd0)
                    #period;
                if(memory_request_ready_0 == 1'd1) begin
                    sim_memory[address * 8+:8] = data;
                    if(address[0] == 1'd0)
                        memory_response_0 = sim_memory[address * 8+:16];
                    else
                        memory_response_0 = sim_memory[(address - 1) * 8+:16];
                    memory_response_ready_0 = 1'd1;
                    while(data_out_ready_0 == 1'd0)
                        #period;
                end
            end
            else begin
                cpu_request_1 = { 1'd1, data, address };
                cpu_request_ready_1 = 1'd1;
                while(data_out_ready_1 == 1'd0 && memory_request_ready_1 == 1'd0)
                    #period;
                if(memory_request_ready_1 == 1'd1) begin
                    sim_memory[address * 8+:8] = data;
                    if(address[0] == 1'd0)
                        memory_response_1 = sim_memory[address * 8+:16];
                    else
                        memory_response_1 = sim_memory[(address - 1) * 8+:16];
                    memory_response_ready_1 = 1'd1;
                    while(data_out_ready_1 == 1'd0)
                        #period;
                end
            end

            cpu_request_0 = 25'd0;
            cpu_request_1 = 25'd0;
            cpu_request_ready_0 = 1'd0;
            cpu_request_ready_1 = 1'd0;
            memory_response_0 = 16'd0;
            memory_response_1 = 16'd0;
            memory_response_ready_0 = 1'd0;
            memory_response_ready_0 = 1'd0;

            check_data(`SIM_MEMORY_BYTE(address), cpu);

        end
    endtask

    /* Read data from address, check value against memory */
    task read_value_and_check;
        input [15:0] address;
        input cpu;
        begin
            #period;
            if(cpu == 0) begin
                cpu_request_0 = { 1'd0, 8'd0, address };
                cpu_request_ready_0 = 1'd1;
                while(data_out_ready_0 == 1'd0 && memory_request_ready_0 == 1'd0)
                    #period;
                if(memory_request_ready_0 == 1'd1) begin
                    if(address[0] == 1'd0)
                        memory_response_0 = sim_memory[address * 8+:16];
                    else
                        memory_response_0 = sim_memory[(address - 1) * 8+:16];
                    memory_response_ready_0 = 1'd1;
                    while(data_out_ready_0 == 1'd0)
                        #period;
                end
            end
            else begin
                cpu_request_1 = { 1'd0, 8'd0, address };
                cpu_request_ready_1 = 1'd1;
                while(data_out_ready_1 == 1'd0 && memory_request_ready_1 == 1'd0)
                    #period;
                if(memory_request_ready_1 == 1'd1) begin
                    if(address[0] == 1'd0)
                        memory_response_1 = sim_memory[address * 8+:16];
                    else
                        memory_response_1 = sim_memory[(address - 1) * 8+:16];
                    memory_response_ready_1 = 1'd1;
                    while(data_out_ready_1 == 1'd0)
                        #period;
                end
            end

            cpu_request_0 = 25'd0;
            cpu_request_1 = 25'd0;
            cpu_request_ready_0 = 1'd0;
            cpu_request_ready_1 = 1'd0;
            memory_response_0 = 16'd0;
            memory_response_1 = 16'd0;
            memory_response_ready_0 = 1'd0;
            memory_response_ready_1 = 1'd0;

            check_data(`SIM_MEMORY_BYTE(address), cpu);
        end
    endtask

    /* Makes sure that data_out is the expected 8 bit value */
    task check_data;
        input [7:0] expected;
        input cpu;
        begin
            if(cpu == 0) begin
                if(data_out_0 != expected) begin
                    $display("[ERROR] result:%d expected:%d\nError on Line Number = %0d",data_out_0,expected,`__LINE__);
                    $stop;
                end
            end
            else begin
                if(data_out_1 != expected) begin
                    $display("[ERROR] result:%d expected:%d\nError on Line Number = %0d",data_out_1,expected,`__LINE__);
                    $stop;
                end
            end
            
        end
    endtask

    initial begin
        reset_cache();

        $display("[status] beginning tests");

        $display("[test] writing different data to same location from each cpu");
        write_value_and_check(8'd16, 16'd23, 0);
        write_value_and_check(8'd25, 16'd23, 1);
        read_value_and_check(16'd23, 0);
        read_value_and_check(16'd23, 1);
        read_value_and_check(16'd23, 0);

        write_value_and_check(8'd255, 16'd34, 1);
        read_value_and_check(16'd34, 0);
        read_value_and_check(16'd34, 1);
        write_value_and_check(8'd128, 16'd34, 1);
        read_value_and_check(16'd34, 0);
        read_value_and_check(16'd34, 1);

        $display("[test] resetting cache, setting first and last 2000 addresses, reading from random cpu");
        reset_cache();
        for(i = 0; i < 2000; i = i + 1) begin
            `SIM_MEMORY_BYTE(i) = $random();
        end
        for(i = 65535; i > 63535; i = i - 1) begin
            `SIM_MEMORY_BYTE(i) = $random();
        end

        for(i = 0; i < 6000; i = i + 1) begin
            random_cpu = $random() %2; 
            read_value_and_check(i[15:0], random_cpu);
        end

        $display("[test] writing and checking both cpus");
        for(i = 0; i < 2000; i = i + 1) begin
            test_addy[15:0] = $random();
            test_data[7:0] = $random();
            random_cpu = $random() %2;

            write_value_and_check(test_data[7:0], test_addy[15:0], random_cpu);
            if(random_cpu == 0)
                read_value_and_check(test_addy[15:0], 0);
            else
                read_value_and_check(test_addy[15:0], 1);
        end

        $display("[status] all tests passed :)");
        $stop;
    end
endmodule