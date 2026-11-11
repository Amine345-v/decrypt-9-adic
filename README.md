Cryptanalytic Engine & Polynomial-Time Inversion Suite for Collatz PRGs
and Cryptosystems via Backward p-Adic Hensel Peeling and Dyadic Cylinders.

Implements and benchmarks:

1. Algorithm 1 (9-Adic Switch-Block Inverter for Mode A):
   Recovers secret key u in {0,1}^M and secret seed n_0 from public terminal state
   y = S^{2M}(n_0) satisfying 9^M n_0 + B_{2M}(u) = 16^M y in O(M^2) time with
   trellis width strictly 1. Decrypts ciphertext P = C (+) hash(n_0, u) in polynomial time!
2. Algorithm 2 (3-Adic Hensel Peeling for Binary Alphabet Sigma = {1, 2}):
   Given terminal state y and alphabet Sigma = {1, 2}, reconstructs the unique
   valuation sequence w in {1, 2}^m and initial seed n_0 in O(m^2) time with trellis width 1.
3. Algorithm 3 (Dyadic Cylinder Recovery from Keystream):
   Inverts keystream segments and recovers secret seeds when 2-adic cylinder hints
   or keystream parity blocks are leaked.
4. Comprehensive empirical benchmark suite across key lengths:
   M in {16, 32, 64, 128, 256, 512, 1024} bits.
   Saves full timing benchmarks, polynomial degree scaling fits (log-log regression),
   and 100% decryption success rates to `crypto_2_results.json`.