`include "macros.vh"

/* Cache Coherenter (Yes that is a word, don't even)
* Takes in an address of one cache that is change and sends it to the other 
* to have the validity bit set to 0
*/


module cache_coherenter(
    input clock, reset,
    input [24:0] cache_change_0, cache_change_1,
    output reg [15:0] cache_invalidate_0, cache_invalidate_1
);

    always @(posedge clock) begin
        if(!reset) begin
            cache_invalidate_0 <= 16'd0;
            cache_invalidate_1 <= 16'd0;
        end
        else begin
            if(cache_change_0[`CPU_REQUEST_COMMAND] == `WRITE)
                cache_invalidate_1 <= cache_change_0[`INVALIDATE_ADDRESS];
            if(cache_change_1[`CPU_REQUEST_COMMAND] == `WRITE)
                cache_invalidate_0 <= cache_change_1[`INVALIDATE_ADDRESS];
        end
    end
endmodule