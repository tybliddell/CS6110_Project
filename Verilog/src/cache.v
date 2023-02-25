`include "macros.vh"

module cache(
    input [24:0] cpu_request, /* 1 bit for r/w, 8 bits for data, 16 bits for address */
    input cpu_request_ready, /* cpu_request is populated, ready for processing */
    input clock, input reset,
    input [15:0] invalidate_address, /* coming from controller, invalidate that entry */
    input [15:0] memory_response, /* 16 bits for data */
    input memory_response_ready,
    output reg [24:0] memory_request, /* 1 bit for r/w, 8 bits for data, 16 bits for address */
    output reg memory_request_ready, /* memory_request is populated, ready for processing */
    output reg [7:0] data_out, /* return data to cpu */
    output reg data_out_ready /* return data to cpu is ready */
);

    /* 1 bit for valid, 8 bits for tag, 16 bits for data */
    reg [`NUM_VALIDITY_BITS + `NUM_TAG_BITS + `CACHE_BITS_PER_BLOCK - 1:0] cache_mem[`CACHE_BLOCK_COUNT-1:0]; 

    // States
    integer i;
    parameter RESET = 3'd0;
    parameter IDLE = 3'd1;
    parameter _IDLE = 3'd2;
    parameter COMPARE_TAG = 3'd3;
    parameter WAIT_ON_MEMORY = 3'd4;
    parameter _WAIT_ON_MEMORY = 3'd5;
    reg [2:0] state = IDLE;
    reg [2:0] next_state = IDLE;
    reg [15:0] last_invalidate;

    always @(posedge clock) begin
        if(!reset)
            state = RESET;
        else
            state = next_state;

        // match in cache_mem
        if(invalidate_address != last_invalidate) begin
            if(cache_mem[invalidate_address[`INVALIDATE_ADDRESS_INDEX]][`CACHE_MEM_TAG] == invalidate_address[`INVALIDATE_ADDRESS_TAG]) begin
                cache_mem[invalidate_address[`INVALIDATE_ADDRESS_INDEX]][`CACHE_MEM_VALIDITY] <= 1'b0;
            end
        end
        
        last_invalidate <= invalidate_address;
        data_out <= data_out;
        memory_request <= memory_request;

        case(state)
            RESET: begin
                for(i = 0; i < `CACHE_BLOCK_COUNT; i = i + 1) begin
                    cache_mem[i][`NUM_VALIDITY_BITS + `NUM_TAG_BITS + `CACHE_BITS_PER_BLOCK - 1:0] <= {`NUM_VALIDITY_BITS + `NUM_TAG_BITS + `CACHE_BITS_PER_BLOCK{'d0}};
                end
                memory_request <= 25'd0;
                memory_request_ready <= 1'd0;
                data_out <= 8'd0;
                data_out_ready <= 1'd0;
                next_state <= IDLE;
            end
            IDLE, _IDLE: begin
                if(cpu_request_ready)
                    next_state <= COMPARE_TAG;
                else
                    next_state <= state == IDLE ? _IDLE : IDLE;
                memory_request <= 25'd0;
                memory_request_ready <= 1'd0;
                data_out <= data_out;
                data_out_ready <= 1'd0;
            end
            COMPARE_TAG: begin
                // Read
                if(cpu_request[`CPU_REQUEST_COMMAND] == 1'b0) begin
                    // cache_mem[][]
                    // if cache entry tag matches cpu_request tag and is valid
                    if(cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_TAG] == cpu_request[`CPU_REQUEST_TAG]
                        && cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_VALIDITY] == 1'b1) begin
                        memory_request <= 25'd0;
                        memory_request_ready <= 1'd0;
                        if(cpu_request[`CPU_REQUEST_OFFSET] == 1'b0)
                            data_out <= cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_DATA_LOWER];
                        else
                            data_out <= cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_DATA_UPPER];
                        data_out_ready <= 1'd1;
                        next_state <= IDLE;
                    end
                    // cache entry is not present or valid
                    else begin //Miss
                        memory_request <= { `READ, 8'd0, cpu_request[`CPU_REQUEST_ADDRESS] };
                        memory_request_ready <= 1'd1;
                        data_out <= data_out;
                        data_out_ready <= 1'd0;
                        next_state <= WAIT_ON_MEMORY;
                    end
                end
                //Write
                else begin
                    // Write to cache, and send a memory request
                    cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_TAG] <= cpu_request[`CPU_REQUEST_TAG];
                    cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_VALIDITY] <= 1'd1;
                    if(cpu_request[`CPU_REQUEST_OFFSET] == 1'b0)
                        cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_DATA_LOWER] <= cpu_request[`CPU_REQUEST_DATA];
                    else
                        cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_DATA_UPPER] <= cpu_request[`CPU_REQUEST_DATA];
                    memory_request <= { `WRITE, cpu_request[`CPU_REQUEST_DATA], cpu_request[`CPU_REQUEST_ADDRESS] };
                    memory_request_ready <= 1'd1;
                    data_out <= data_out;
                    data_out_ready <= 1'd0;
                    next_state <= WAIT_ON_MEMORY;
                end
            end
            WAIT_ON_MEMORY, _WAIT_ON_MEMORY: begin
                if(memory_response_ready == 1'b1) begin
                    //write memory_response to cache
                    cache_mem[cpu_request[`CPU_REQUEST_INDEX]][`CACHE_MEM_DATA] <= memory_response;
                    data_out_ready <= 1'd1;
                    memory_request <= 25'd0;
                    memory_request_ready <= 1'd0;
                    if(cpu_request[`CPU_REQUEST_OFFSET] == 1'b0)
                        data_out <= memory_response[`MEMORY_RESPONSE_LOWER];
                    else
                        data_out <= memory_response[`MEMORY_RESPONSE_UPPER];
                    next_state <= IDLE;
                end
                else begin
                    next_state <= state == WAIT_ON_MEMORY ? _WAIT_ON_MEMORY : WAIT_ON_MEMORY;
                    memory_request <= memory_request;
                    memory_request_ready <= 1'd1;
                    data_out <= data_out;
                    data_out_ready <= 1'd0;
                end
            end
            default: begin
                next_state <= IDLE;
                memory_request <= 25'd0;
                memory_request_ready <= 1'd0;
                data_out <= 8'd0;
                data_out_ready <= 1'd0;
            end            
        endcase
    end
endmodule