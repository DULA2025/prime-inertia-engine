import cupy as cp
import time
import math

print("--- INITIATING PIE v33.0: MULTI-BIT QUANTUM TUNNELING ---")
print("TARGET: Break the 65-Friction Hamming Trap (n=668)")
print("UPGRADE: Simultaneous Multi-Bit Flips Enabled")

t = 42

def random_sequence(length):
    return cp.where(cp.random.randint(0, 2, length) == 0, -1, 1).astype(cp.int8)

def calc_npaf_shift(seq, shift):
    if shift >= len(seq): return 0
    return cp.sum(seq[:-shift] * seq[shift:])

def calculate_turyn_friction(A, B, C, D):
    total_friction = 0
    for s in range(1, t):
        npaf_A = calc_npaf_shift(A, s)
        npaf_B = calc_npaf_shift(B, s)
        npaf_C = calc_npaf_shift(C, s)
        npaf_D = calc_npaf_shift(D, s) if s < (t - 1) else 0
        total_friction += abs(int(npaf_A + npaf_B + npaf_C + npaf_D))
    return total_friction

def turyn_tunneling_miner(max_iterations=3000000):
    A, B, C, D = random_sequence(t), random_sequence(t), random_sequence(t), random_sequence(t-1)
    sequences = [A, B, C, D]
    
    current_friction = calculate_turyn_friction(*sequences)
    best_friction = current_friction
    
    temperature = 80.0  
    cooling_rate = 0.99999 
    flatline_counter = 0
    iteration = 0
    start_time = time.time()
    
    while current_friction > 0 and iteration < max_iterations:
        # QUANTUM TUNNELING: Decide how many bits to flip simultaneously
        # 90% chance for 1 bit, 10% chance to jump the Hamming gap (2 to 4 bits)
        num_flips = 1
        if cp.random.rand().item() < 0.10:
            num_flips = cp.random.randint(2, 5).item()
            
        flip_records = []
        
        # Execute the simultaneous flips
        for _ in range(num_flips):
            seq_idx = cp.random.randint(0, 4).item()
            seq_len = t if seq_idx < 3 else (t - 1)
            
            # Maintain the Tail-Bias logic
            if cp.random.rand().item() < 0.7:
                tail_bound = int(seq_len * 0.3)
                if cp.random.rand().item() < 0.5:
                    flip_idx = cp.random.randint(0, tail_bound).item()
                else:
                    flip_idx = cp.random.randint(seq_len - tail_bound, seq_len).item()
            else:
                flip_idx = cp.random.randint(0, seq_len).item()
                
            sequences[seq_idx][flip_idx] *= -1 
            flip_records.append((seq_idx, flip_idx))
            
        test_friction = calculate_turyn_friction(*sequences)
        delta_E = test_friction - current_friction
        
        # Metropolis-Hastings Acceptance
        if delta_E < 0 or (cp.random.rand().item() < math.exp(-delta_E / temperature)):
            current_friction = test_friction
            if current_friction < best_friction:
                best_friction = current_friction
                flatline_counter = 0 
        else:
            # Revert ALL simultaneous flips if the jump failed
            for seq_idx, flip_idx in flip_records:
                sequences[seq_idx][flip_idx] *= -1 
                
        temperature = max(temperature * cooling_rate, 0.01)
        flatline_counter += 1
        iteration += 1
        
        if flatline_counter > 30000 and temperature < 2.0:
            print(f"\n[!] HAMMING TRAP DETECTED AT {current_friction}. ENGAGING 100-DEGREE OVERCHARGE...")
            temperature = 100.0  # <--- NEW OVERCHARGE TEMPERATURE
            flatline_counter = 0
            print(f"[!] TEMPERATURE SPIKED TO 100.0. MAXIMUM QUANTUM BOIL ENGAGED.\n")
        
        if iteration % 10000 == 0:
            elapsed = time.time() - start_time
            print(f"PASS {iteration:06d} | Temp: {temperature:.3f} | Best Fric: {best_friction} | Cur Fric: {current_friction} | Flips: {num_flips} | Time: {elapsed:.2f}s")
            start_time = time.time()

    return sequences, best_friction

try:
    final_seqs, final_fric = turyn_tunneling_miner()
    if final_fric == 0:
        print("\n==================================================")
        print(">>> HOLY GRAIL DISCOVERED: TURYN SEQUENCES FOUND!")
        print("==================================================")
        with open('turyn_42_42_42_41_sequences.txt', 'w') as f:
            f.write(f"A ({t}): {cp.asnumpy(final_seqs[0]).tolist()}\n")
            f.write(f"B ({t}): {cp.asnumpy(final_seqs[1]).tolist()}\n")
            f.write(f"C ({t}): {cp.asnumpy(final_seqs[2]).tolist()}\n")
            f.write(f"D ({t-1}): {cp.asnumpy(final_seqs[3]).tolist()}\n")
        print("DATA CRYSTALLIZED TO: turyn_42_42_42_41_sequences.txt")
    else:
        print(f"\n[!] MINING CYCLE PAUSED. Lowest Friction Reached: {final_fric}")
except Exception as e:
    print(f"CRITICAL FAULT: {e}")
