`timescale 1 ns/10 ps

module collector_emitter_tb;
    localparam period = 20;
    localparam half_period = period / 2;
    reg clock, reset;
    reg collector_serial_in, collector_ready;
    wire [24:0] collector_data;
    wire collector_data_ready;

    reg [24:0] emitter_data_in;
    reg emitter_data_in_start;
    wire emitter_serial_out;
    wire emitter_serial_out_done;
    wire [24:0] e_collector_data;
    wire e_collector_data_ready;

    input_collector #(.OUTPUT_WIDTH(25)) collector_uut(.serial_in(collector_serial_in), .fast_clk(clock), .ready(collector_ready), .data(collector_data), .reset(reset), .data_ready(collector_data_ready));
    
    output_emitter #(.INPUT_WIDTH(25)) emitter_uut(.data(emitter_data_in), .fast_clk(clock), .start(emitter_data_in_start), .serial_out(emitter_serial_out), .serial_done(emitter_serial_out_done), .reset(reset));
    input_collector #(.OUTPUT_WIDTH(25)) collector(.serial_in(emitter_serial_out), .fast_clk(clock), .ready(emitter_serial_out_done), .data(e_collector_data), .reset(reset), .data_ready(e_collector_data_ready));
    integer i;

    always #half_period begin
        clock = ~clock;
    end
 
    task reset_collector;
        begin
            clock = 1'b0;
            reset = 1'b1;
            collector_serial_in = 1'd0;
            collector_ready = 1'd0;
            #period;
            reset = 1'd0;
            #period;
            reset = 1'd1;
            #period;
            $display("[status] reset collector");
        end
    endtask

    task collector_check_data;
        input [24:0] expected;
        begin
            if(collector_data != expected) begin
                $display("[ERROR] result:%d expected:%d\nError on Line Number = %0d",collector_data,expected,`__LINE__);
                $stop;
            end
        end
    endtask

    task collector_check_ready_signal;
        begin
            if(collector_data_ready != 1'd1) begin
                $display("[ERROR] expected collector_data_ready signal to be high\nError on Line Number = %0d",`__LINE__);
                $stop;
            end
        end
    endtask

    task collector_write_data;
        input [24:0] wdata;
        begin
            collector_ready = 1'd0;
            for(i = 0; i < 25; i=i+1) begin
                collector_serial_in = wdata[i];
                #period;
            end
            collector_ready = 1'd1;
            #period;
        end
    endtask

    task reset_emitter;
        begin
            clock = 1'd0;
            reset = 1'd1;
            emitter_data_in = 25'd0;
            emitter_data_in_start = 1'd0;
            #period;
            reset = 1'd0;
            #period;
            reset = 1'd1;
            #period;
            $display("[status] reset emitter");
        end
    endtask

    task emitter_check_data;
        input [24:0] expected;
        begin
            if(e_collector_data != expected) begin
                $display("[ERROR] result:%d expected:%d\nError on Line Number = %0d",collector_data,expected,`__LINE__);
                $stop;
            end
        end
    endtask

    task emitter_write_data;
        input [24:0] wdata;
        begin
            #period;
            emitter_data_in_start = 1'd1;
            emitter_data_in = wdata;
            for(i = 0; i < 27; i=i+1) begin
                #period;
            end
            emitter_data_in_start = 1'd0;
        end
    endtask

    initial begin
        $display("[status] beginning tests on collector");
        reset_collector();
        collector_check_data(25'd0);
        collector_write_data(25'd3461);
        collector_check_data(25'd3461);
        collector_check_ready_signal();

        collector_write_data(25'd69);
        collector_check_data(25'd69);
        collector_check_ready_signal();
        
        reset_collector();
        collector_write_data(25'h1FF_FFFF); // All 1s
        collector_check_data(25'h1FF_FFFF);
        collector_check_ready_signal();
        
        reset_collector();
        collector_write_data(25'd0);
        collector_check_data(25'd0);
        collector_check_ready_signal();


        $display("[status] beginning tests on emitter");
        reset_emitter();
        emitter_write_data(25'h1FF_FFFF);
        emitter_check_data(25'h1FF_FFFF);

        emitter_write_data(25'd69420);
        emitter_check_data(25'd69420);

        $display("[status] all tests passed :)");
        $stop;
    end
endmodule