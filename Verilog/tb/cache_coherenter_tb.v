`timescale 1 ns/10 ps

module cache_coherenter_tb;
    localparam period = 20;
    localparam half_period = period / 2;
    reg clock, reset;
    reg [24:0] cache_change_0, cache_change_1;
    wire [15:0] cache_invalidate_0, cache_invalidate_1;

    cache_coherenter uut(.clock(clock), .reset(reset), .cache_change_0(cache_change_0), .cache_change_1(cache_change_1), 
                          .cache_invalidate_0(cache_invalidate_0), .cache_invalidate_1(cache_invalidate_1)
    );

    always #half_period begin
        clock = ~clock;
    end
    
    initial begin
        cache_change_0 = 25'd0;
        clock = 1'd0;
        #period;
        cache_change_0 = {1'd1, 8'd123, 16'd100};
        #period;
        $display("cache invalidate should be %d", cache_invalidate_1);
    end
endmodule