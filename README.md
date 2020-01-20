# bitsofcotton/randtools
Simple PRNG and omplement to PRNG. So there's export limiation on the law, none for here.

# En/Decryption - SHA - PRNG
There exists entropy decreasingly loop on them, might be precederes exists.

* En/Decryption -> SHA
  d'_k := En/Dec(d_k,d_k+1), d^{n}_k =: SHA
* SHA -> En/Decryption
  xor key for d_k: SHA(d_0, ..., d_k-1, d_k+1, ..., d_n,KEY)
* PRNG -> SHA
  internal state: PRNG(a_0), d0 := permutate bits : d ^ PRNG, d0'_k := d0_k ^ d0_k+1, d0{n}_k := SHA
* SHA -> PRNG
  r_0 := SHA(time, uptime, entropy), r_k+1 := SHA(r_k, counter, deterministic entropy)
* En/Decryption -> PRNG
  r_0 := En/Dec(time, uptime, entropy), r_1 := entropy, r_k+1 := En/Dec(r_k, r_k-1, counter, deterministic entropy)
* PRNG -> En/Decryption
  a(PRNG, k) * in + b(PRNG, k) in F_p(PRNG, k), for each blocks, shifts, minimum rand blocks and maximum rand another blocks en/dec.

* Simple PRNG
  
