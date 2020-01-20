# bitsofcotton/randtools
Simple PRNG and complement to PRNG. So there's export limiation on the law, none for here.

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
  based on transcendal numbers generater taylor series, so with no complicated series, the structure
  for x = x_0 + x_1 * p' + x_2 * p'^2 + ... numbers, f(x):=a_0+a_1*x+a_2*x^2+..., 
  f(x):=&lt;[1,x,x^2,...],a&gt;, so with F_(p^k), x_l:=&lt;a'_l,[1,x]&gt;, f(x)|_F_(p^k) = Sum_l a''_l*[1, x_l],
  for them, b_k:=f(x)|coefficient of y_k, y := y_0 + y_1 * p' + ... == f(x)|_F_(p^k).
  For results, b_k/b_k+1, k for pair steps.  
  But for this, f(x) fundementally only shuffles entropy, so collecting entropy is the matter.
