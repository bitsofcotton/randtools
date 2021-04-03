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
After general tips 4, we can write d/dx\_l op == Pi\_l \<y'\_l, x\> with decreasing degree on them, so recursive on this, d/dx\_l ... op == \<y\*, x\>. And if we can define g(op) == f^{-1}(op) when x_n:=1, f(op)==d/dx_1 ... d/dx_{n-1} op == \<y\*,x\> (first digit) (this is done by general tips 4), and, g^n(op) = det(Y' x\*(x\_1\*...x\_n)), so to make f(g^n(f^{n-1}(op))), replace x\_k to x\_k^{n-1}, ok. if we use this conversion (x\_k to x\_k^m) into middle of the transform, it fails. And, x':=x\*x_1\*...\*x_n replace is needed per n degree.

# General Tips 6
There exists taylor series tan((op_{first digit}-.5)&pi;/3) == det diag B x on some cut off.
(rank tan(op) == 2 because we make const. delta).
With below, we get op\_{near bit} == \<y\*\*,\[1,x\]\>\*(x_1\*...)^some m .

This is also checked with for 2 input, nand operation inverse matrix eigenvalue is smaller than 0.23.

# General Tips 7
Once we get such operations on n bit to n bit conditions, y=Ax with some error condition on most digit condition.
If we are lucky, we can define invert condition. But this doesn't directl mean P==NP, so complexity itself applys
into accuracy on A matrix and x vector on (x_1\*...\*x_n)^m meaning, m depends accuracy and complexity.
But in invariant meaning, R^1 multiply is ~.

# General Tips 8
So with below, A in Q^{n\*n} : random matrix, x in {0, 1}^n, Ax in first digit meaning seems to harden the PRNG
if original PRNG is better enough (long period and no bias on distribution.).

# General Tips 9
If we work with F\_p p in P, this description is also valid because x in F\_p, #((ax+b)|\_x:fix)==#(F\_p to F\_p) .
so zero condition is valid. (with lagrange multipliers, all condition is valid with op_{first digit} with general tips 4, 5 method with n to p\*n.).
So p-adic computer is also described with lagrange multipliers and same methods, by op_{first digit}, this is in Z.
So tan phase with &pi; / (p + 1), we can make any operation on them as \<y,\[1,1/x_1,...,1/x_n\]>\*(x\_1...x\_n)^some m, x in {0,...,p-1}^n,
y in Q^{n+1} with some error
when we input x\_k into x\_k^((n-1)-n). we can take last atan(tan(...)) part as inverse part series, ... part is described as \<y,\[1,x\]\>\*
(x\_1...x\_n)^some m,
and we can take some taylor series on 1 / atan(tan(...)) = Pi(\<a_k,\[1,\<y,\[1,x\]\>\]\>), So this with p frequency with x\_k^p on op_{first digit},
we can take \<y,1/x_1,...,1/x_n\>\*(x_1...x_n)^some m==1/op so if inverse is exists, p-adic computer is ok on this description. So the matrix we look with p-adic is
inverse input and output matrix, not the one we should take.

This is also checked with for 1 input, {x} for {1,...,p}, \[..., \[1, 1/k, 1/&alpha;\_k\], ...\] matrices eigen value limit,
but this is the limit of another p' larger than p. If we use recursive of sum and the projection, it's ok with some error cut off.

and op == f, op':=f(x_1,...,x_n)-x_n+1=g(x_1,...,x_n+1), we have invariant, in this case, we can get g as \<y, \[1,x\]\> == 0 condition.

If we work with x\_k in \[0, &alpha;\[ that float styled, the description \<y,\[1,1/x_1,...,1/x_n\]\> form is valid also in this method
because integer styled numerator F\_p and denominator fixed exists. With this description and invariant below, x\_n+1:=\<y,\[1,x_1,...,x_n\]\>
condition is valid for \]- &alpha;, &alpha;\[ register computer but also with this, it's inverse condition matrix that we have.

# General Tips A
If we deal with large enough matrix \[x_2,..,x_{n+1}\]:=A\[x_1, ..., x_n,1\] (if original matrix is smaller than A, it is also valid),
with shrinking range \[x_0,...,x\_m,1\], m\<n, the shrinked range is described as : \[x\_{n+1},...,x\_{n+1+m}\]:=B\[x_0,...,x_m,1\]
because each x_k is described as \<a_k,\[...,\<a\_{k}\_{k+1},...,\[x\_0,...,x\_m,1\],...,...\>,...\]\>.
So step some range and get invariant value is also valid operation if larger one function recursion exists.  
Some random methods compete with this s.t. permutation after making rand() series, but this results only larger original matrix.

N.B. this is the case PRNG initial stage smaller count than status variable dimensions.
So this isn't mean some distant result is written in smaller variable dimensions.

N.B. if we have a extreme enough accuracy, we can write down the condition x_n to x_n+x_{n-1}\*a^-k+..., so all of inner condition and
before state is represented by only one variable. So in this case, we can take the condition below A.row(A.rows() - 1), but in general,
the condition needs extremely high accuracy for vector a and input, it's not.

# General Tips B
If we have x_n := \<a,\[x_0,...,x_{n-1}\]\>, if we have {x_{kn}}, it's only recursive on A matrix, this causes p0 prediction valid.

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU
* https://osdn.net/projects/bitsofcotton-randtools/

# Archive
This repository is archived, so without bugreport, will no change. 2021/02/09 version is archived. It's ok. 2021/02/15 version is ok for retest. 2021/02/17 recheck ok, sleeping, 2021/02/24 sleep 2, 2021/02/07 sleep3, bug report is welcomed.
