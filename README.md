# bitsofcotton/randtools
Simple PRNG and complement to PRNG. So there's export limiation on the law, none for here.

There exists entropy decreasingly loop on them, might be precederes exists.

* En/Decryption -> SHA
  d'\_k := En/Dec(d_k,d_k+1), d^{n}\_k =: SHA
* SHA -> En/Decryption
  xor key for d_k: SHA(d_0, ..., d_k-1, d_k+1, ..., d_n,KEY)
* PRNG -> SHA
  internal state: PRNG(a_0), d0 := permutate bits : d ^ PRNG, d0'\_k := d0_k ^ d0_k+1, d0{n}\_k := SHA
* SHA -> PRNG
  r\_0 := SHA(time, uptime, entropy), r\_k+1 := SHA(r\_k, counter, deterministic entropy)
* En/Decryption -> PRNG
  r\_0 := En/Dec(time, uptime, entropy), r\_1 := entropy, r\_k+1 := En/Dec(r\_k, r\_k-1, counter, deterministic entropy)
* PRNG -> En/Decryption
  a(PRNG, k) * in + b(PRNG, k) in F_p(PRNG, k), for each blocks, shifts, minimum rand blocks and maximum rand another blocks en/dec.
* Simple PRNG
  (Originaly from my context, around 2004 sekitanbukuro -> around 2010's osayudo -> then, here, but, there might be preceders on other places.)  
  based on transcendal numbers generater taylor series, so with no complicated series, the structure
  for x = x_0 + x_1 * p' + x_2 * p'^2 + ... numbers, f(x):=a_0+a_1\*x+a_2\*x^2+..., 
  f(x):=&lt;\[1,x,x^2,...\],a&gt;, so with F_(p^k), x_l:=<a'\_l,\[1,x\]>, f(x)|\_F\_(p^k) = Sum_l a''\_l*\[1, x\_l\],
  for them, returns y_k s.t. y := y_0 + y_1 * p' + ... == f(x)|\_F\_(p^k).
  But for this, f(x) fundementally only shuffles entropy, so collecting entropy is the matter.
  N.B. with F_p'^2, it has a slight possibility to calculate whole f(x) with only their accuracy, but it's not,
  so F_(p'^p') accuracy is able to do them.  
  To harden this, please refer p2.
* Simple PKI (pre shared key):  
  PSend(Decrypted): PKI Pair(Key1, Decrypted, Key1', Random):  
    ALICE(Key2, Key1, Decrypted, Key1', Random) <=> BOB(Key3, Key1', Random, PEnc(Decrypted, (Key1, Key1', Random))  
      ALICE <=> TORRENT(Key2, Key3) : Enc(Enc(Key1, SHA(Key1, Decrypted, Key1', Random)), Key2)  
      ALICE  => BOB(Key1', Random)  : PEnc(Decrypted, (Key1, Key1', Random))  
                                    : Enc(Decrypted, SHA(Enc(Key1, SHA(Key1, Decrypted, Key1', Random)), Key1', Random))  
      TORRENT(Key2, Key3) <=> BOB   : Enc(Enc(Key1, SHA(Key1, Decrypted, Key1', Random)), Key3)  
      BOB                           : PDec(PEnc(...), (Dec(Enc(Enc(...), Key3), Key3), Key1', Random))  
                                    : Dec(PEnc(...), SHA(Dec(Enc(Enc(Key1, SHA(...))), Key1', Random))  
  ALICE <=> BOB : By PSend(MSG) chain, make MSG, MSG, MSGOK, MSGOK, timenow, timenow.  
  But, there's no such protocols.
  
# General Tips
With 2^x:=\[1, x_0, ...,x_n, x_0 and x_1, ..., x_{n - 1} and x_n, ..., x_0 and ... and x_n\] form, the operation 'and' and 'not' is described as A in R^{N\*N}, A\*2^x, and recursive of another similar matrixes is also in them, so any functions that inputs n bits and output n bits, they can be described as R^{N\*N} matrix.  
So with good PRNG, such random matrix A and A \* 2^x seems to harden the original prng series. 

# General Tips 2
If we deal with if ... else ... methods, if we can have x_k := ifthenbit, we can handle them with
if ... block with A, else ... block with B, x_k\*A + (1-x_k)\*B matrix.

# General Tips Tips
2^x is defined by x and all combination on latter one are in the former one.
Because of this, the matrix describes any of the peano's axiom valid neuman computer program input to output relation.

# General Tips 3
If we deal them with psnd alternative unsafe algorithms, it believes outside of peano's axiom that to be A subset 2^N, B subset N, A/~ ~2 B/~3 on N, ~3 == id.
I don't know whether this is valid or not for calculating only with n bits on left and right on 2^x meanings.  
If we can't deal with them, please check conv_check alternatives.

# General Tips 4
Otherwise, suppose x in {0, 1}^{n0}, Xor\_k And\_m Xor\_n x\_{k,m,n}\*x\_n == any operation on them (And Xor ... is pattern match for 1 pattern, (a xor b) xor (a and b) == (a or b)). So with op == Sum\_k det diag (X\_k x) == det(diag(Y x)), this is done by GSVD {X\_0, X\_1} == {U R\_0 V, U R\_1 V}, decompose 2 of them, then, all of them, and, this is able to be done because X\_k in Z^{n\*n} (not {0, 1}^{n\*n}).  
So any op == det diag(Y x), x\_0:=1, x in {0, 1}^n, Y in Q^{n\*n}. (This is also because any taylor series are in this form x\_k in {0, 1} if some hyper plane have zero function value.)  
det diag(Y x) == \<y, x\> because \<a,x\>\<b,x\> == \<A x + b, x\> == \<b, x\> + \<&Lambda;x', x'\> == \<b, x\> + Sum &lambda;\_k\<u\_k,x\>\<u\_k,x\> == \<b, x\> + Sum &lambda;\_k\<u\_k, x\> == \<c,x\>, recursive.

# General Tips 5
x^+=f(x) case, with general tips 4, x^+\_k:=det(Y\_k x), so with Z.row(k):=(Y\_k^{-1}).row(k), if we can define Y\_k^{-1} as reasonable one, we can define g(x^+)=x 's g := h\[Z\].

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU

# Archive
This repository is archived, so without bugreport, will no change.
