/*
* Expects serial_in to be sent in starting with the least significant bit.
* Send in OUTPUT_WIDTH worth of data, waiting for one clock cycle after each
* THEN pull ready high and wait another clock cycle.
*/
module input_collector
#(parameter OUTPUT_WIDTH = 16)
(
    input serial_in,
    input fast_clk,
    input ready,
    input reset,
    output reg [OUTPUT_WIDTH-1:0] data,
    output reg data_ready
);

    always @(posedge fast_clk) begin
        if(!reset) begin
            data <= {OUTPUT_WIDTH{1'd0}};
            data_ready <= 1'd0;
        end
        else if(!ready) begin
            data <= { serial_in, data[OUTPUT_WIDTH-1:1] };
            data_ready <= 1'd0;
        end
        else if(ready) begin
            data_ready <= 1'd1;
        end
    end
endmodule