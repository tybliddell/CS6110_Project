/* 
    Murphi model for a two cache system

    rumur --output cache.c repo/model/cache.m
    cc -std=c11 -O3 -o cache cache.c -lpthread -mcx16
    ./cache
*/

const
    N_CACHE_ENTRIES: 2
    N_CACHES: 2

type 
    cache_id: 0 .. N_CACHES - 1
    entries: 0 .. N_CACHE_ENTRIES - 1

    command: enum {READ, WRITE, INV} -- READ, WRITE come from CPU, INV comes from coherenter

    cache_entry_valid: array[entries] of boolean
    last_entry_command: array[entries] of command
    read_req: -1 .. N_CACHE_ENTRIES - 1
    
    cache: record
        valid: cache_entry_valid -- array of whether each entry is valid
        last_cmd: last_entry_command -- array for last cmd for each entry
        req: read_req -- -1 if no request OR the index of memory location cache is asking for
    end;

var
    caches: array[cache_id] of cache

startstate begin
    -- Begin caches in idle with all entries invalid, no memory request --
    for i: cache_id do
        caches[i].req := -1;
        for j: entries do
            caches[i].last_cmd[j] := INV;
            caches[i].valid[j] := false;
        end;
    end;
end

ruleset i: cache_id; j: entries do
    rule "Write to valid"
        caches[i].valid[j] -- This entry is valid
        & caches[i].req == -1 -- Cache is not waiting for memory
        ==>
    begin
        caches[i].valid[j] := true; -- Valid after write 
        caches[i].last_cmd[j] := WRITE;

        for k: cache_id do
            if(k != i) then -- For each other cache, must invalidate
                caches[k].valid[j] := false; -- No longer valid
                caches[k].last_cmd[j] := INV;
            end;
        end;
    end
end

ruleset i: cache_id; j: entries do
    rule "Write to invalid"
        !caches[i].valid[j] -- This entry is invalid
        & caches[i].req == -1 -- Cache is not waiting for memory
        ==>
    begin
        caches[i].valid[j] := true; -- Valid after write
        caches[i].last_cmd[j] := WRITE;
        for k: cache_id do
            if(k != i) then -- For each other cache, must invalidate
                caches[k].valid[j] := false; -- No longer valid
                caches[k].last_cmd[j] := INV;
            end;
        end;
    end
end

ruleset i: cache_id; j: entries do
    rule "Read from valid"
        caches[i].valid[j] -- This entry is valid
        & caches[i].req == -1 -- Cache is not waiting for memory
        ==>
    begin
        caches[i].last_cmd[j] := READ;
    end
end

ruleset i: cache_id; j: entries do
    rule "Read from invalid"
        !caches[i].valid[j] -- This entry is invalid 
        & caches[i].req == -1 -- Cache is not waiting for memory
        ==>
    begin
        caches[i].req := j; -- Make a memory request
        caches[i].last_cmd[j] := READ;
    end
end

ruleset i: cache_id do
    rule "Respond to read"
        caches[i].req != -1 -- Cache is waiting for memory
        ==>
    begin
        caches[i].valid[caches[i].req] := true; -- That entry requested is now valid for that cache
        caches[i].last_cmd[caches[i].req] := READ;
        caches[i].req := -1; -- Cache is no longer waiting for memory
    end
end

-- Define invariants for correct execution
invariant "Both cannot write last and be valid"
forall i: cache_id do
    forall j: cache_id do
        forall k: entries do
            i != j -> -- For every pair of caches, and for each entry in both
            ((caches[i].last_cmd[k] == WRITE & caches[j].last_cmd[k] == WRITE) -> (!caches[i].valid[k] & !caches[j].valid[k]))
        end
    end
end;

invariant "If both are valid, at least one must be a read"
forall i: cache_id do
    forall j: cache_id do
        forall k: entries do
            i != j -> -- For every pair of caches, and for each entry in both
            ((caches[i].valid[k] & caches[j].valid[k]) -> (caches[i].last_cmd[k] == READ | caches[j].last_cmd[k] == READ))
        end
    end
end;

invariant "If last command was INV, should be invalid. If WRITE or READ from existing, should be valid"
forall i: cache_id do
    forall k: entries do
        -- If the entry was invalidated, it should not be valid
        (caches[i].last_cmd[k] == INV -> !caches[i].valid[k])
        -- If just wrote an entry, or read from entry that didn't need to go to memory, should be valid
        & ((caches[i].last_cmd[k] == WRITE | (caches[i].last_cmd[k] == READ & caches[i].req == -1)) -> caches[i].valid[k])
    end
end;