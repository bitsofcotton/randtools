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
Otherwise, suppose x in {0, 1}^{n0}, Xor\_k And\_m Xor\_n x\_{k,m,n}\*x\_n == any operation on them (And Xor ... is pattern match for 1 pattern, (a xor b) xor (a and b) == (a or b)). So with op == Sum\_k det diag (X\_k x) == det(diag(Y x)), this is done by counter diagonal method and LDLt with inverse matrix because X\_0 and X\_1 is max rank and 1 \< rank (det diag(X\_0^-1X\_1 x)+det diag(x) == det diag (LDL^t \[x, x\]) + det diag\[x, x\] == det diag LDx' + det diag L^{-t}x', so upper left or right down part factor makes them, then, unitary, recursive.), decompose 2 of them, then, all of them, and, this is able to be done because X\_k in Z^{n\*n} (not {0, 1}^{n\*n}). (a and b) is larger double by (a xor b), but whole of this, it's correct.  
So any op == det diag(Y x), x\_0:=1, x in {0, 1}^n, Y in Q^{n\*n}, in first digit meaning.

# General Tips 5
After general tips 4, we can write log(op) == Sum\_k log(\<y\_k, x\>), with d/dx\_l log(op) == Sum\_k y\_k\_l / \<y\_k, x\>, so we can write op\*d/dx\_l log(op) == d/dx\_l op == Pi\_l \<y'\_l, x\> with decreasing degree on them, so recursive on this, d/dx\_l ... op == \<y\*, x\>. And if we can define g(op) == f^{-1}(op) when x_n:=1, f(op)==d/dx_1 ... d/dx_{n-1} op == \<y\*,x\> (first digit), this is done by x^2==x if x in {0, 1} and general tips 4 decomposition. And we can't eliminate last x\_k's coefficient because the x\_k meaning itself had to changes if so, otherwise, we can integrate and can make differential.

# General Tips 6
After general tips 5, we can handle sin(&pi;/2\*(op_{first digit} - 0.5 + f(op_{first_digit},&pi;)) with some error cut off can define no first digit condition
but the most bit condition with absolute value.
Since op_{first digit} is holomorphic, sin(op_{first digit}) = \<y\*,x\>(1 pm\<y\*,x\>/&pi;)\*... == det diag B x on some cut off.
(rank sin(op) == 2 then this).
With below, we get op\_{most bit} == abs(\<y\*\*,x\>), (= \<y\*\*,x\>\<y\*\*,x\> = \<exists B x,x\>).
(but this has a numerical errors that we can handle for any error rate larger than 0.)   
N.B. abs(x)==sqrt(x^2) is not in C^1 but in C^0, so weak taylor series can exists, but since rank op == 1,
so we can't handle in the form \<y\*\*,x\> with abs nor x^2 as the form them, lagrange multiplier neither.

# General Tips 7
Once we get such operations on n bit to n bit conditions, y=abs(Ax) with some error condition on most digit condition.
so log y = 2 log(Ax) condition, if we are lucky, we can define invert condition.

# General Tips 8
So with below, A in Q^{n\*n} : random matrix, x in {0, 1}^n, abs(Ax) in first digit meaning seems to harden the PRNG
if original PRNG is better enough (long period and no bias on distribution.).

# General Tips 9
If we work with F\_p p in P, this description is also valid because x in F\_p, #((ax+b)|\_x:fix)==#(F\_p to F\_p) .
so zero condition is valid. (with lagrange multipliers, all condition is valid with recursive of sin ... 's f  in General Tips 6. #{x^k, x: fix, forany k}=p)
So p-adic computer is also described with sum det(X x) form (but X in Q^{some m\*n}) so with abs(\<y,x\>) form y in Q^n.

If we work with x\_k in \[0, &alpha;\[ that float styled, the description abs(\<a,x\>) form is valid with some error also in this method
because integer styled numerator F\_p and denominator fixed exists.

# General Tips A
If we deal with large enough matrix \[x_2,..,x_{n+1}\]:=abs(A\[x_1, ..., x_n,1\]), with shrinking range \[x_0,...,x\_m,1\], m\<n,
the shrinked range is described as : \[x\_{n+1},...,x\_{n+1+m}\]:=abs(B\[x_0,...,x_m,1\]) because each x_k is described as
abs(\<a_k,\[...,\<a\_{k}\_{k+1},...,\[x\_0,...,x\_m,1\],...,...\>,...\]\>). So step some range and get invariant value
is also valid operation with small error if larger one function recursion exists.  
So to prevent this, some random methods compete with this s.t. permutation after making rand() series, so multiply and first
digit method is also in them.

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU
* https://osdn.net/projects/bitsofcotton-randtools/

# Archive
This repository is archived, so without bugreport, will no change. 2021/02/09 version is archived. It's ok. 2021/02/15 version is ok for retest. bug report is welcomed.
