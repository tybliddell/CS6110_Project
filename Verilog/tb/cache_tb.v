`timescale 1 ns/10 ps
`define SIM_MEMORY_BYTE(address) sim_memory[address * 8+:8] 
`define SIM_MEM_SIZE (65_536*8) - 1

module cache_tb;
    localparam period = 20;
    localparam half_period = period / 2;

    reg[`SIM_MEM_SIZE:0] sim_memory;
    integer i;

    reg[24:0] cpu_request;
    reg[15:0] invalidate_address, memory_response;
    reg clock, reset, cpu_request_ready, memory_response_ready;

    wire [24:0] memory_request;
    wire [7:0] data_out;
    wire data_out_ready, memory_request_ready;

    cache uut(.cpu_request(cpu_request), .cpu_request_ready(cpu_request_ready), .clock(clock), .reset(reset),
    .invalidate_address(invalidate_address), .memory_response(memory_response), .memory_response_ready(memory_response_ready), 
    .memory_request(memory_request), .memory_request_ready(memory_request_ready), .data_out(data_out), .data_out_ready(data_out_ready));

    always #half_period begin
        clock = ~clock;
    end

    /* reset the cache to all invalid, inputs to 0, and sim_memory to 0 */
    task reset_cache;
        begin
            clock = 1'b0;
            reset = 1'b1;
            cpu_request_ready = 1'd0;
            memory_response_ready = 1'd0;
            cpu_request = 25'd0;
            invalidate_address = 16'd0;
            memory_response = 16'd0;
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
        begin
            #period;
            cpu_request = { 1'd1, data, address };
            cpu_request_ready = 1'd1;

            while(data_out_ready == 1'd0 && memory_request_ready == 1'd0) begin
                #period;
            end
            // simulate memory
            if(memory_request_ready == 1'd1) begin
                sim_memory[address * 8+:8] = data;
                // starting at address * 8 bits going to address * 8 + 16 bits
                if(address[0] == 1'b0)
                    memory_response = sim_memory[address * 8+:16];
                // starting at (address - 1) * 8 bits going to (address - 1) * 8 + 16 bits
                else
                    memory_response = sim_memory[(address - 1) * 8+:16];
                memory_response_ready = 1'd1;
                // wait for data
                while(data_out_ready == 1'd0) begin
                    #period;
                end
            end

            cpu_request = 25'd0;
            cpu_request_ready = 1'd0;
            memory_response = 16'd0;
            memory_response_ready = 1'd0;

            check_data(`SIM_MEMORY_BYTE(address));
        end
    endtask

    /* Read data from address, check value against memory */
    task read_value_and_check;
        input [15:0] address;
        begin
            #period;
            cpu_request = { 1'd0, 8'd0, address };
            cpu_request_ready = 1'd1;
            while(data_out_ready == 1'd0 && memory_request_ready == 1'd0) begin
                #period;
            end
            // simulate memory
            if(memory_request_ready == 1'd1) begin
                // starting at address * 8 bits going to address * 8 + 16 bits
                if(address[0] == 1'b0)
                    memory_response = sim_memory[address * 8+:16];
                // starting at (address - 1) * 8 bits going to (address - 1) * 8 + 16 bits
                else
                    memory_response = sim_memory[(address - 1) * 8+:16];
                memory_response_ready = 1'd1;
                // wait for data
                while(data_out_ready == 1'd0) begin
                    #period;
                end
            end

            cpu_request = 25'd0;
            cpu_request_ready = 1'd0;
            memory_response = 16'd0;
            memory_response_ready = 1'd0;

            check_data(`SIM_MEMORY_BYTE(address));
        end
    endtask

    /* Makes sure that data_out is the expected 8 bit value */
    task check_data;
        input [7:0] expected;
        begin
            if(data_out != expected) begin
                $display("[ERROR] result:%d expected:%d\nError on Line Number = %0d",data_out,expected,`__LINE__);
                $stop;
            end
        end
    endtask

    task invalidate;
        input [15:0] address;
        begin
            #period;
            invalidate_address <= address;
            #period;
        end
    endtask

    initial begin
        reset_cache();

        $display("[status] beginning tests");

        $display("[test] writing and reading multiple times to addresses in same block");
        write_value_and_check(8'd55, 16'd12);
        write_value_and_check(8'd56, 16'd13);
        read_value_and_check(16'd12);
        read_value_and_check(16'd13);
        write_value_and_check(8'd34, 16'd13);
        read_value_and_check(16'd13);
        write_value_and_check(8'd21, 16'd12);
        read_value_and_check(16'd12);
        read_value_and_check(16'd13);
        read_value_and_check(16'd12);
        write_value_and_check(8'd1, 16'd13);
        write_value_and_check(8'd4, 16'd12);
        read_value_and_check(16'd12);
        read_value_and_check(16'd13);

        $display("[test] writing and reading to addresses in adjacent blocks");
        write_value_and_check(8'd34, 16'd14);
        write_value_and_check(8'd127, 16'd15);
        read_value_and_check(16'd14);
        read_value_and_check(16'd13);
        write_value_and_check(8'd137, 16'd12);
        read_value_and_check(16'd15);
        read_value_and_check(16'd12);

        $display("[test] writing to block 0");
        write_value_and_check(8'd21, 16'd0);
        write_value_and_check(8'd23, 16'd1);
        read_value_and_check(16'd0);
        read_value_and_check(16'd1);

        $display("[test] writing to block 65534/65535");
        write_value_and_check(8'd33, 16'd65534);
        read_value_and_check(16'd65534);
        write_value_and_check(8'd34, 16'd65535);
        read_value_and_check(16'd65535);

        $display("[test] resseting cache, setting sim_memory to 0, and reading all values");
        reset_cache();
        for(i = 0; i < 65535; i = i + 1) begin
            read_value_and_check(i[15:0]);
        end
        
        $display("[test] resetting cache, setting random values in sim_memory, and reading all values");
        reset_cache();
        for(i = 0; i < 65535; i = i + 1) begin
            `SIM_MEMORY_BYTE(i) = $random();
        end
        for(i = 0; i < 65535; i = i + 1) begin
            read_value_and_check(i[15:0]);
        end

        $display("[test] invalidate entry after writing");
        write_value_and_check(8'd15, 16'd16);
        invalidate(16'd16);
        read_value_and_check(16'd16);

        $display("[status] all tests passed :)");
        $stop;
    end
endmodule