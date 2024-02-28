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
(Add 2022/12/26 first, g^n(op), then, operate with below, then, f^n causes +const. reduce the original glitch.)

# General Tips 5
After general tips 4, we can write d/dx\_l op == Pi\_l \<y'\_l, x\> with decreasing degree on them, so recursive on this, d/dx\_l ... op == \<y\*, x\>. And if we can define g(op) == f^{-1}(op) when x_n:=1, f(op)==d/dx_1 ... d/dx_{n-1} op == \<y\*,x\> (first digit) (this is done by general tips 4), and, g^n(op) = det(Y' x\*(x\_1\*...x\_n)), so to make f(g^n(f^{n-1}(op))), replace x\_k to x\_k^{n-1}, ok. if we use this conversion (x\_k to x\_k^m) into middle of the transform, it fails. And, x':=x\*x_1\*...\*x_n replace is needed per n degree.

This is also checked by partial integrals that: integrate det diag Y x dx_k == x_k det diag Y x - integrate x_k d/dx_k det diag Y x and d/dx_k them.

# General Tips 6
There exists taylor series tan((op_{first digit}-.5)&pi;/6) <strike>== (det diag B x) \* (x_1 ...)^some m / (det diag B' x) / (x_1 ...)^some m on some cut off.
(<strike>rank sin, cos(op) == 2 because we make const. delta,</strike>pass all of the first large dimension multipliers into sin, cos taylors, then, do below, we can get the result. tan theta itself cannot be used because they doesn't converges).
With below, we get op\_{near bit} == \<y\*\*,\[1,x\]\>/\<y'\*\*,\[1,x\]\>.
</strike>(2023/10/09 we cannot expand taylor series without adding periods on each det diag B because of factoring them slips).

# General Tips 7
punched.

# General Tips 8
So with below, A in Q^{n\*n} : random matrix, x in {0, 1}^n, Ax in first digit meaning seems to harden the PRNG
if original PRNG is better enough (long period and no bias on distribution.).

# General Tips 9
If we work with F\_p p in P, this description is also valid because x in F\_p, #((ax+b)|\_x:fix)==#(F\_p to F\_p) .
so zero condition is valid. (with lagrange multipliers, all condition is valid with op_{first digit} with general tips 4, 5 method with n to p\*n.).
So p-adic computer is also described with lagrange multipliers and same methods, by op_{first digit}, this is in Z.
<strike>We can also take op == \<y_0,x\>/\<y_1,x\>, x in {p, 1, ..., p - 1}^n with some extra small error.</strike>(2023/10/09 same reason tips 6)

p-adic is also checked by toeplitz(x) \* a == f(x) linear permutation, because a\*x+b\+... describes them.

and op':=op(x_1,...,x_n)-x_n+1=some f(x_1,...,x_n+1), we have invariant, in this case, we can get g as \<y, tan(\[1,x,s\])\> == 0 condition, s is status bits. Status bit is needed because of rank condition, but, s can be rewrited as some A\*\[1,x\].

N.B. we should choose \<y, arctan(\[1,x\])\> with this form, but arctan has not have periods in itself. To make periods valid, we choose tan(a\*y):=tan(Ax) to adjust them, so using invariant, each of variables are rewrited to be A\<y,tan(\[1,x,B x\])\>.

If we work with x := {x\_k in \[0, &alpha;\[} that float styled, the description \<y,tan(\[1,x,A\*x\])\> form is valid also in this method. So with this, \[- &alpha;, &alpha;\[ can be.

# General Tips A
If we deal with large enough matrix <strike>tan(\[1,x+,B\*x+\]):=A\*tan(\[1,x,B\*x\]),
with smaller A', tan(\[1,x(small)+,B'\*x(small)+\])=
A'\*tan(\[1,x(small),B'\*x(small)\]).</strike>(2023/10/09 simpler one) tan \<a,x\>.
So step some range and get invariant value is also valid operation if larger one function recursion exists.  
Some random methods compete with this s.t. permutation after making rand() series, but this results only larger original matrix.

N.B. this is the case PRNG initial stage smaller count than status variable dimensions.
So this isn't mean some distant result is written in smaller variable dimensions.

N.B. if we have a extreme enough accuracy, we can write down the condition x_n to x_n+x_{n-1}\*a^-k+..., so all of inner condition and
before state is represented by only one variable. So in this case, we can take the condition below A.row(A.rows() - 1), but in general,
the condition needs extremely high accuracy for vector a and input, it's not.

# General Tips B
If we have x_n := \<a,tan(\[1,x,B\*x\]\>, if we have {x_{kn}}, it's only recursive on A matrix, this causes p0 prediction valid.

# General Tips C
Some deep learning gets matrices on the result and after all, it's only a matrix. So with invariant meaning,
with <strike>A\[tan(x) tan(B\*x) tan(y) tan(C\*y)\]-&gt;0</strike>(2023/10/09 simpler one)tan A\[x, y\] matrix.
So if we can find an invariant on the data series with some expanded dimensions, we can define a mapping.

# General Tips D
punched.

# General Tips E
Only for invariant meaning, we can bet 0==arcsin(sin(\<a, x\>)) on the form<strike>, so it's also the form 0==\<a, x\>\*(x_1...x_n)^m (exists m for some error).
So linear invariant meaning from the data, it's also the form: \<d_k, x\>\/(x_1...x_n)^m is ok. So d_k into variable, it's \<d_k, x\>\/(d_1...d_n)^m.</strike>(2023/10/09 same reason tips 6).
if we ~ with only ratio on them, it's \<d_k, x\>\/(d_1...d_n)^(1/n).

# General Tips F
The factor algorithm are described with \[2, ..., n\] == exp(Factor(log(\[p\_1, ..., p\_m\]))).
This guarantees us to analyse some well-described structures with some of the small sized structures (from dimension differences).
However, if the data we treat referes out of the (or larger than) p\_m prime, the structure referes some non measurable condition.
So first hypothesis upper bound size is the matter to rationally analyse something.
(Factor difference firstly appear \[2, 3, 5\] vs. \[2, 3, 4, 5\] size. So elementary function they supports some of the world by rationally could be categorizable 3 to 5 kind of them.)

However, in this meaning, the function combination theirselves also have number upper bounds.
Especially, 2 operand operator can be described as 4x4 matrix and so with this, 5^(&alpha;\*4\*4) pattern could describe any with some compression method (especially with \{compress\} \{decompress\} matrix for each size or whole of the size includes R).
There's 3 or more operand operators, we cannot shrink them into such size.
So with above, if first hypothesis is not enough size, this either fails.

Even so, if the \{compress\} or \{decompress\} isn't consistent, the whole hypothesis fails in this General Tips F.

(One of the \{compress\} matrix is described as Factor matrix relation with Factor matrix with some log condition. But with the geometry, they have g != 0. Also, if such \{compress\} has consistent, the geometry of them are alike sheet between sheet with some collision.)

# General Tips G
If the input stream is from some observed points that we can make the hypothesis there's a (im\|ex)plicit repeat operation on the stream as a structure, General Tips F concludes there's some 3 to 5 root descriptions they make some combination into original stream.

However, we can always make imitated implicit repeat operation on original stream, so if the stream has enough representation on the phenomenon, the structure will.

# General Tips H
Therefore, we can focus the high layer invariant eg. (f (h a b)) == (g (f a) (f b)) like symbolic ones. (This is named as logarithm with f == log, g == +, h == *. As we based on N, so they're possible simple enough.)
But this is already done before or around 19century for most of the parts, and after then, with (f A) == (B) like group theory method instead of them also already done by some of the large efforts. So we should refer them first (by some of the search engine or some of the GPT based Q&A service.)

# General Tips I
To take invariant on any of f makes some information convergence.
This is because: #{(x,y)|y=f(x),x in {0,1}^n, y in {0,1}} == 2^(n+1),
also: #{f|y=f(x),x in {0,1}^n, y in {0,1}} == 2^(2^n).
Taking invariant causes input counting, making much combination causes
output complexity counting.

A 1-valued 1-output combination causes invariants in the vector up to aleph_0 dimension, so high layer of them, structure text invariant (like a lisp but we can make any of the operators into 2 operand of them each) causes vector up to aleph_1 dimension.
With below, the complexity remains up to aleph_1 combination on f output counting meaning. However, if we separate x vector as some separation not to be fixed size, it's up to aleph_omega causes x\rightarrow n combination.
So, if we take fixed size input and we can separate them as clear to 2 operand operators on them, it's up to aleph_1 combination.
However, if we can take invariants on such of them, it's up to 2^(n+1) combination.

# General Tips J
General Tips I doesn't generate paradoxical dilemma, however, is also have them.

This is because counting up (x,y) stands for their invariants, on the opposite site, counting up f stands for any of f combination.
The scope invariant have is only dim x, either f have any of dimensions larger or equal to them.
They causes y+:=f(x+) function we construct them by y:=g(x) s.t. dim x+==dim x + 1.
One of the example is f(x+):=&lt;A[x,x'],[x,x']&gt; structure they gets f(x+)==g(x)*g(x)+x'*x'+&lt;Bx,ux'&gt;.
This is out of the invariant description, however, inside on the f definition.

Either, however, in the meaning of combination on the scope, they also have dilemma on the description because {0,1}-invariant generated datas have up to 2^((n+1)^2), f-complexity generated datas have down to 2^(2^n).

I don't have any clue on this to describe rationally in mathematical manner.

# General Tips K
However, to check general tips I,J, we need to check the table down to the size 256x256x16 and each size 5 bit. This is because we cannot check them by binary operation theirselves. I didn't check them, however, in the context on this document, they might slips from some of the reason.

# General Tips L
With calculating lower bound:
* 2 term: 2^2^2 : 2^3^2
* 3 term: 2^2^3 : 2^4^2
* 4 term: 2^2^4 : 2^5^2
* 5 term: 2^2^5 : 2^6^2
* 6 term: 2^2^6 : 2^7^2

So larger than 2^2^6 table with 2^7 \* 7 bit data we should check them then.
The 6 term with no raw group operation inside them could cause R^13 vector for the function, if we reduce and concat them, it's R^7 for each. Our magic number is up to 7 in general (the wide known experiment result the larger than them sometimes described as a number block of telephone region or so.). So they might from our limitation.

# General Tips M
General Tips J, K, L might be caused by counting the element of aleph_aleph_omega.
Since we can only construct constructive elements upto aleph_omega when we're using the element of the set who have cardinal up to aleph_..., so they might be caused by some of the outside but catched by some ~.
We might say some of the multiple of perspective can causes, if they are true, one of the perspective principle of combination is from: to count up (x, y) or to count up f-complexity.
Also, multiple of the perspective could attach the information part when the object is not tangled enough.

# General Tips N
The difference comes along with General Tips L might be described as: tan(Ax*f(x)+Bx*(1-f(x))).
This is to make +1 dimension on input with some of the f(x) internal structure representation because x:=\[variable, const\].
However, they also be in the function tan(Cx).

So almost any of the function, they make some fix on the structure itself, they causes +1 dimension invariant, also causes some of the information entropy glitches they exclude some another phenomenon nor another complexity combination as a operator. Some of the beautiful method on mathematics exclude them into infinite far away, they could cause no attach on original.

# General Tips O
The variable length data encoding with General Tips N causes some collision on glitches, they causes dimension barrier not to work with, so they cannot be described with fixed tan(Cx).

This also causes General Tips L, however, the field {N, ...} sheets collision.

In the worst collision cases, a != a and a == a for any N', a != a for indirect proof, a == a for inside out a == a and a != a on N, #N'&lt;~1024.

# General Tips P
There's a possibility we have such illegal process because of breaking dimension barrier.
In such case, Genral Tips N meaning, f(x) to be some of the dimension statistics, \[variable, const\] not to be clear divided.

They might come from some of the over complexity after we get cut on invariant.
So in such case, f\_0(x):=tan(\<a,x\>), then, f\_1(x):=tan(\<a,x\>\*f(x)-\<b,x\>\*(1-f(x))) causes over complexity on first order.
They might become s.t. tan\<c,x\> but c\_k ~0.111.... we cannot decide 1 continues inifinite digit or not.

However, even in such case, we can decide them by expanding into ternaly series, then, binary series in some cut off.

I have no idea for them but they might come from multiple meaning into single meaning cohesion.

# General Tips Q
Recalculate General Tips L, it's to go:
* 2^2^1 : 2^(2\*3/2)
* 2^2^2 : 2^(3\*4/2)
* 2^2^3 : 2^(4\*5/2)
* 2^2^4 : 2^(5\*6/2)
it's down to 4.

(cf.) There exists S^4 as some weired differential automorphisms.
In unary series numbered into some surfaces, then, break some of the dimension barrier could causes \]n,n+1\[~phi reductions, however, they'll get also 1 to 1 maps.

We make first hypothesis as clearly dividable some of the number elements.
So to break dimension barrier causes collition to them.
So they might be caused by dimension barrier transformation between some of the vector sets as non separatable ones.

So with them, we might calculate some of the arithmetic N operators with some context treat as some geometrical spaces, they might not on minkovski ones.
We believe prime factoring some of the numbers causes original arithmetic space to minkovski one but, this isn't proved and we don't know how to treat such ways.

# General Tips R
Even the perspective from classical physics, the situation unchange.

In such system, especially in the classical eletctronics, it's the problem with closed loop the circuit have. Ordinal systems has a variational approach description which only depends on closed circuit of the calculator we implement.
So it's on the problem with only (x,y,z) except transient phenomenon.
This relates on each parts consistency on mathematics.

However, on the context meaning, there exists 4d each electron locus manifold problem.
So logic gates larger than 4 bit, if there's some uncertain dimensions we cannot configure, (in the meaning to General Tips Q, it's some of the tanglements which cannot described as a bit, literally ((might be, or my inet connection is broken) no known conversion on entanglement on modern physics)), there's also the possibility, but normaly they depends only on some of the PDEs depends only on the closed circuits.

If we describe them as a logic gates (and we can do them), they also causes PDEs, have the case division.
(i)   to begin with, it's a stationary value, so it's access to the initial value or beyond them.
(ii)  it's deterministic, even we cannot believe, it's true N/~0 ~2 N/~1 in physical meaning on some spaces.
(iii) it's only open end, we get/set some of the value related to some object.
(iv)  it's optimization problem stationary value, so we don't decide prior which constraints to be fixed without referring initial value.

So situation unchanges...

# General Tips S
When prime factoring some number, it's a description of the number recursively operator + recursive.
This referes plain object as operator +, then, abstract algorithm operator +, then, algorithm repeat operator +, ....
These recursive doesn't have upper limit of recursive number.
So the result is inverse problem of n-th order operator + references.
If there's some decomposition route to stack some-order operator ..., they can be multiple definition of result.
This is the condition General Tips R (ii) one of a description.

However, N is p.i.d., so I don't have the clue why something strange occurs when we calculate contradiction, and why we can do such calculation.

# General Tips T
Calculating such contradiction in abacus, we need table function and branch condition by statistics other than operator \*,\/,\+,\-.
In such view, to take statistics and to make branch condition by them can causes such something strange with calculation and their inverse collision.
However, the operation is reeled as observation after and before calculation, might causes invariant information cohesion.

# General Tips U
When we apply their collision into variable number, #{f(x,y,z)} doesn't collide variable to variable, however, #{f(x,y,z,w)} has collision, from General Tips Q.
So C\*C has some structure their selves because they exclude some series of the functions, also, H has internal structure.
In this meaning, (x,y,z,t) has some structure they excludes.

This is weired conclusion, however, if we make some of the hypothesis, they excludes some of the structures. So we might have a-priori structure they depends on first hypothesis.

In below tracking logic, commonly we don't need to matter the dimension barrier or #f collide if the hypothesis we first make is concrete for the a-priori structure, however, even so, we can think about breaking the barrier after some of the discussion made.

In general, they're reeled into larger system PDEs, come along with some of the initial values.

# General Tips V
There might exist predecessors around C*-algebra, but, in General Tips I concludes f : R to R is constructed by counting invariant meaning s.t.:
g_0, g_1, g_2 : 0 a.e., some value on countable definition region, i, j, k : R^infty, f(x)==wavelet(wavelet(fourier(i(theta)) + g_0(x), j(theta')) + g_1(x), k(theta'')) + g_2(x).
This conflicts C : aleph_0 on information amount meaning, however, in counting invariant meaning and in counting complexity meaning, latter one C^C, former one 2^aleph_0^2. This is to make decomposition on original f into mother wavelet with subtracting countable uncontinuous points, causes aleph_0 information subtraction, to untie combination causes 2^... glitch, twice causes 2^C^2, result mother wavelet causes aleph_0 information. We estimate.

# General Tips W
However, our starting point is to take operator +, operator \* causes decompose combinations by {f(x)=x, f(x)=exp(x)}.
If there exists valid logic parallel to us, they might be {f(x)=exists g(x), f(x)=exists h(x)} decomposition by first definition on the structures.
This is because f(x,y,z) : worst case valid number of the variables, we take hypothesis f(x,1,status), then, subtract the structures twice causes their valid structures.

The amount f(x,y,z) variable number is not a real upper bound of the variables concrete enough, however, if we make the dimension barrier breaking glitch, larger variable number causes unstable nor historical dependant or hypothesis dependant result.
They might come along with treating some of the variants of the same description, same meaning, another contexts causes some glitch, we take them as a observing or a initial value or a skid.

# General Tips X
(A function index estimate has glitches on this context, however, this can be caused by untie some of the combination.)
To take irrational number into tan description, we should make some + dimension on input to same variable.
However, we cannot make infinite series by tan(ax+b) description, a, b in R, |a|&gt;&gt;1 because they doesn't converges in calculation because of the base increases larger and larger.
If they converges, any of the R to R is described by (a_0, b_0), ..., (a_5, b_5) as coded in first order (non irrational coefficients case.) (also this can be coded into one number of R).
Starting from the number (a_0, ..., b_5) in R^12, x in \[0,1\] f(x) in \[-1,1\] can changes the situation, however, in general, they doesn't converge in constructive method, so they're only one of the descriptions.

# General Tips Y
If the #f glitch has some relation to tanglement and observation, we can define a time machine bit without such machine if only some parts has glitch and almost any of the parts are concretely constructed by constructive methods.
Otherwise, only out of the computation box can effect such bit.

However, v2v tanglement says only up to 3 variable is better to do with, so to verify such program works well or not excites the heavy problem which I don't know whether we can decompose them or not.

One angle to decompose then is to make algorithms into tan Ax form, then, analyse A's transgress. However, I either don't know what method can describe them well (could someone knows).

# General Tips Z
We can think about the glitch as maximum closed set as #A == aleph_omega and breaking dimension barrier causes #B == aleph_(2^omega).
This don't describe them enough in details.
So this only causes shirks them in the view of each description consistency into context of actual infinite when we apply them as takinig invariant infinitely recursive.
(However, actual infinite can be larger than them when we think first combination of the f as worse steep one. So they are possible infinite even so.)

# General Tips AA
However, if the original calculation box is described in physical calculator, there's some loophole to decide such inconsistent values in optimization problem.
We might be able to handle them with such loophole, QC with another conceptual way calculation on classical machine.

# General Tips AB
Breaking dimension barrier causes breaking original hypothesis s.t. low of the excluded middle.
This causes making meaning to {} itself, nor, some of the stack of consistent bricks to be some of the inconsistent.
However, we don't know whether or not breaking dimension equivalent to invariant countup glitch.

# General Tips AC
From 2018 memo, gather their results with these results causes:

(Hypothesis-i) The finite or possible infinite combination of consistent object is consistent.
(Hypothesis-i-sub) {} exists. Also, we can divide any of the groups into some of the sub groups including {}.

Makes N well, also with possible infinite, they makes element e in A, #A &lt; aleph_omega.

(Hypothesis-ii) We can adopt multiple-valued low of excluded middle.

Makes Logics and Boole algebra. (Logics only ennames the induction switch cases which excludes middle.). Also, the negated predicate makes f in B, #B ~ aleph_(2^omega) the function space also breaks dimension barrier as a view of A.

We believe existence of A and B as a different ones, however, the randtools optimizer causes B ~ A as a observation calculation. There is much glitch to count up them, however, the anchor of their observation might given by many much amount of calculation theirselves nor observation their selves. The lower limit of the order for n-bit observation might calculation in O(n^4) if the former one is true.

# General Tips AD
Instead of general tips R, (v) it is from and to the gulf of factor prime number sparsity itselves seems to be true.
We calculate the abstract of them as physical way, it's also no use when writing down as a optimization condition.
The conditions needs to be fixed and the status we get is to write down them in calculate as tan(A [x status]) == x+ condition.
So A meets status block, we cannot describe well them.

So they might from the factor algorithm exp(F(log([2, ...]))) F's sparsity, so it's orthogonal to F matrix, however, other conditions are not defined as well.

# General Tips AE
Correction to tips <strike>AE</strike>AD, (vi) it is from the topology the whole calculation PDE have.

If we suppose the original algorithm as PDE, the system has its topology.
So if their topology is different to some of the others', the calculation might slips.

In this case, the p\[456\] needs the data read/write is to depend the topology and tangle with original algorithms causes topology change causes calculation slips.

# General Tips AF
However, tips AE depends on eigen values on A in tan Ax description on external of the calculation algorithm itself they believes what we believes that consistent and no illegal to dimension barrier.
After observing some of the system, they can be described as x+ := tan Ax calculation, so they're described as x+ = tan A'B'C'x and they say the illegal response depends on B' 's structure. So they also caused by tan \<a, \[x, 1\]\> description's +1 dimension tricks.

Also, there exists task switching and core switching in ordinary calculation systems.
In the case, it is very hard problem to split what calculation topology we're ruunning.

# General Tips AG
So after observing the glitch, they're described as tips AF so to use \<a, \[x, 1\]\> 's +1 dimension trick, the larger matrix eigen value sign counting condition.

However, before observing the glitch and determining where they're from, it's also from invariant counting glitch.

We don't know the relation between invariant glitch and factoring matrix sparsity glitch.

# General Tips AH
From the invariant glitch viewpoint, factor matrix glitch is self describes as N^infty observations.
So invariant glitch is generalization to them and the viewpoint of them is for N itself and for F_p^k.

Analogy to them, there might exists the view to invariant glitch from the factor matrix glitch viewpoint which I don't know them at all.

# General Tips AI
However, the general tipses <strike>below</strike> above doesn't describes multiple to single condition.

The {compress} and {decompress} can be implemented as deterministic and fixed size input, smaller variable size output pairs (can be exchanged).

So if the whole calculation is deterministic, the information bit size (kolomogorov complexity) has upper limit not so large ones.
This is the contradiction to our observations.

One of the loophole is to depend observer and they rolled in the calculation system.
However, we cannot recognize such ones, it is harder to exist such occasions.

So we don't know enough on the invariant countup glitch and factor matrix glitch.

# General Tips AJ
In +1 dimension meaning, we can write down input/output as tan(B\*C\*tan(A_0 \[tan(... \[tan(A_n \[x, 1\]), 1\] ...), 1\])).

So to treat A_k as sparse dimension part, we can write down them as tan(B\*C\*A\[x,1\]).

The vanishing part of A_k makes v2v tanglements, so codimension of the A':=f(A_0...A_n) causes matrix C's internal/external topology glitch.

This is the analogy of \[2,3,4,...\]=exp(F log(\[2,3,5,...\])) F codimension part glitch.

So the context makes us to pretend as their codimension extension.

However, we don't know enough on them.

# General Tips AK
In the ratio on invariant and factor, it's near 1:log and 1:1/log.

If they're duality, A/factor for some set A might be observation, A/observation might be factor.

However, we cannot conclude them directly.

# General Tips AL
<strike>
The tips 6 insists (ax+b)/(cx+d) ~ f on some of the error for x in {1,2,...}, f in {1,2,...}.

This is also checked as (ax+b)-f\*(cx+d)&leq;epsilon (cx+d), with this form we get: A\[a,b\]\*A\[a,b\]+f^2B\[c,d\]\*B\[c,d\]-2C\[a,b\]\*\[c,d\]&leq;epsilon^2\*B\[c,d\]\*B\[c,d\].

Summing each rows gets \<A'\[a,b,c,d\],\[a,b,c,d\]\>&leq;epsilon^2\<B'\[c,d\],\[c,d\]\>.

With symmetrizing and decompose, \<\[a',b',c',d'\],\[a',b',c',d'\]\>&leq;epsilon^2\<B''\[a',b',c',d'\],\[a',b',c',d'\]\>.

This leads us to \<(I-epsilon^2 B)\[a',b',c',d'\],\[a',b',c',d'\]\>==0.

If we recover the dimensions for 4 variable traced set, det(I-epsilon^2 B) == 0.

This can be done as eigen values for any epsilon, reverse order track this causes: \<A'\[a,b,c,d\],\[a,b,c,d\]\>&leq;epsilon^2\<B'\[c,d\],\[c,d\]\> makes true.
So with all of eigen values (because they can be symmetrized.), we get A'\[a,b\]\*\[a,b\]+f^2B'''\[c,d\]\*\[c,d\]-2C\[a,b\]\*\[c,d\]&leq;epsilon^2\*B'''\[c,d\]\*\[c,d\] makes truely exists.

we can pull back them with orthogonal matrices (from making first hypothesis for them), so they are pulled into which is small epsilon problem for epsilon and orthogonalized vector elements. We can change indices for a,b,c,d, and there's no zero elements on first hypothesis, if the epsilon is small enough, it's done.

However, we didn't calculate in numerical ones.
</strike>
-&gt; recheck done, true in first digit, bad in some higher order digit.(2023/10/09)

# General Tips AM
So with above, the things we matter is concern with N, R grip on the calculater we believe raw N, R shouldn't be effected by macro scale f countup glitch.

In micro meaning, it stands on boolean algebra and constructive methods. This shouldn't slips but in the macro f countup meaning, so this is to take first N, R as index of f, they slips. Worse to describe, we cannot decide by ourself with raw number only theirselves.

Finding N structure by some of the pattern finding can causes index f counting concerns. So white noise structure can be.

To stand raw N, R, we should believe {}-start structure strongly and we must not deviate from law of exclude middles, also should believe N is p.i.d. .
So we cannot load much functions beat with the structure targets.

Also, if we describe some number concept theirselves, with dim x: f(x) meaning, either the structure they exclude, the first start point of f_k structure can be restricted by this meaning depends on the region the concept effects.

# General Tips AN
operator +, operator \* with 2 term if the context space is saturated by them, the structure can be inserted by f countup glitch.

However, in prime number theorem, p(n) &lt;&gt;= n/log(n), so decomposition and reconstruction by invariant either has the myths to some size of the sets.

Also, the operator + might inserts only one genus to \pm\infty and only slides one to one map by one shift, so it's simple enough function if we make a crack some of the structures to monolithic ones concern with tips W. (R.B. ISBN 9784000051538)

So with tips AM, we should collect some start points of {1, f_k, g_k}_k=1^k=n as a viewpoint of bitsofcotton/p3 works.

# General Tips AO
We want to stand raw {} based N without any context dependance.
This is we want to avoid the serious problematic contexts.

One of the solutions to them is to wrap whole contexts as harmless ones the dimension differed to object.
However, we cannot determine the solution and our base numerical calculation whole avoid the harmfull contexts by start point nor in our calculation subject brains.

So we want enthusiastic but, the attacker nor phenomenon nor observer can attack such backbones in principle.

# General Tips AP
The ongoing machine learning methods uses vector/~ which x~rx, r in R.
So tips E, normalizing norm can reduce complexity they causes glitches.

# General Tips AQ
To list up the combinations of the combinations, to count up combinations in flat meaning causes 2^n^2 pattern and referes up to aleph_omega, however, in raw meaning they causes 2^2^n pattern and refers up to aleph_2^omega.

The glitches might come from this count up, however, we don't know why they comes enough.

# General Tips AR
To count with raw N, R could be done by flat enough nor same order parts calculators.

However, some of the macro glitch they makes error tolerance on some context can slips. They might from pure ideology come along with some of the viewpoints, structures, error tolerant structures.

So if we have error correcting methods they describes field N enough dimension to the calculation, the macro glitch might seems hard to slip the calculations.

However, if we exclude such macro glitches, whether our standing point N, R isn't slipped or not is the matter enough.

# General Tips AS
1/x is also fixed in analytical way with cosh, sinh, sqrt(2) scale.
So y/x cannot slips in natural and mod p is naturally implanted into semi order in R.

However, the macro context can slips in their case ever, so whether the dimension independently fix the N or R in the context is saturated or not is the matter in superficial. But even so, the base N or R slips or not is not determined by only theirselves, even it's very hard way to attack.

# General Tips AT
<strike>
The machine learning with log(atan(\[x,y\])\*...\+...)\+... vector can fix anything because original (atan(\[x,y\])\*...\+...)/... can be thought as operator invariant, log(...) can be thought as period doesn't matter however they can be configured as arbitrary error tolerance, logscale(atan(\[x,y\])\*...) also in this form. The original deep learning method needs period to cover arbitrary operators in general.

However, if machine learning targets each bit as learning and ~ with scalar, any of nand circuit is optimized well with the form, and it's stack of them, the form is also valid.
</strike>
-&gt; There exists universal approximation theorem around 1980s-1990s. They insists for any continuous functions with sigmoidal functions.

# General Tips AU
{compress} and {decompress} isn't valid in raw N itself only, this is because fixing N by internal structure makes exclude some of the contradiction they have, however, to make g&gt;1 on them causes the contradicted N vs. {F_p^k}^m internal structure fixed dimension collision.

By making number of g depends on the internal condition makes k -&gt; large, so some of the correctness on contradicted N could be cut by {F_p^k}^m : structure startpoint we make hypothesis it's not contradicted.

We don't know how language to describe them enough around consistency.
So without the language, we cannot use invariant optimization for program binary optimization as well. However, they have some relation with the observation nor saturation of invariant on the space.

# General Tips AV
Making conversation with some of the generative AI (google bard) causes finding the root of the description:

(multiple viewpoint of any description (aleph_aleph_omega))

 -&gt; (focus picking only one viewpoint) : {aleph_omega (single viewpoint), aleph_omega (data)}

 -&gt; for viewpoint, (focus the uniqueness of the whole) : {no contradicted description combination causes no contradicted, multiple (aleph_(2^omega)}

 -&gt; for unique, (focus the finite quantity from the possible infinite) : {finite set (aleph_-1), possible infinite (omega)}

 -&gt; for unique, (focus the subject/object from the whole causes observability) : {invariant, fixed point}, also, subject needs some of the continuity.

 -&gt; we now get from uniqueness of the whole, raw {N (aleph_0), R (aleph_1), f (aleph_2)} also {some of the consistency, continuity, axiom of choice} either {(de)compress? (wrapper for contradiction for some of the ambiguity), phase transition (some of the discontinuity), fixed point (some of the viewpoint crossing point)}

 -&gt; uniqueness of the whole can refer root descriptions of single viewpoint by internal stack of the calculation, this is assured by #f countups, invariant of the 3 of the viewpoint causes internal structures they caused by the observation. This can describe any of the quantitative driven description.

 -&gt; for viewpoint, multiple of the viewpoint causes 3 of the pillar they exists out of the description they are unique on the whole. This is also assured by the #f countup.


 -&gt; for picking viewpoint, picking not only one viewpoint causes {existence of the any of the data (aleph_omega), existence input output edge surface, data tanglement (also, finding the pattern, #f countup)} can be some of the pillar we start with. This could describe any of the quality driven descriptions, but this is obscure.


 -&gt; So the pillar between {N, R, f} and {aleph_omega, in/out surface, #f count up glitch} can mutually support each other.


The ongoing technologies gathers the viewpoints relates on real world tremendous speed, so in the theoretical meaning, we can carry them into the quantity/quality based description on the tree, however, with some of the description they can have, but, tricolor-tree 16-depth can describe them even we have the concrete infinite data patterns so.

However, we don't know how they linked into real world phenomenons, so in the real world phenomenons have hidden internal states they can make misrepresenation of them, the description system itself is incomplete in their meanings.

# General Tips AW
So interpreting the datastream meaning, we can get {single viewpoint (aleph_omega), multiple of the viewpoint (aleph_aleph_omega), the stream has hidden part (aleph_aleph_aleph_omega)} chain.

So this might be used as 3 pillar on them, so we can get aleph_..._aleph_omega as infinite chain result by the combination of them.

# General Tips AX
So return to the myths on the (de)compress? using some of the description on (F_p^k)^m or #f counting, they are described by access to the deviation from the uniqueness of the whole on the single viewpoint, the description causes multiple of the viewpoint out of the consistent pillar, in/output is undefined on the mathematical meaning.

Also, on the tips AW meaning, if we use them to (de)compress, they can access to aleph_..._aleph_omega on the whole, could be the projection around the actual infinite which begin with {const., x, exp(x)} quantity handling.

This can be nonsense description on them the tools we have now, so this is the end of the repository.

# Generall Tips AY
Also, the description AW can have the outside of the whole of the description, they can be treated as the space which we cannot observe at all.

This is also described as the space which cannot have any attention, however, this could be the probability exists. So our understanding is incomplete ever.

This is also described as unconsiousness on the subject. This could be treated by some of the religious ones, or, we don't have enough tools ever, so it's none of our business.

# General Tips AZ
Even if {N,R,f} can describes aleph_(2^omega), we can describe the quantity based almost anything on them depends on the principal axis of uniqueness and observation.
So we cannot find the possible description region differences between natural language and their languages except for the link to real world nor phychological phenomenon and hidden separated internal status.
So if we can describe some of the description on them, they describes structures, so if the structures are saturated by some of the viewpoints, the real world can be affected by some of the description based approaches causes observation slips.
However, there exists fabel of babel's tower.
Either, the pillar outside the consistency can be a caprice and they have a possibility not to depends on us.

# General Tips BA
The most of the group of scientists fight with the consistent structure and ignores contradicted part, this is to make hypothesis {N,R,f} with uniqueness of the whole.

To follow them with only counting input/output structure on the f, there's no contradiction on optimizing f as tan&lt;a,x&gt; structure on the viewpoint of in/output counting.
So the glitches effects the f numbering and their meaning itself, but optimized vector isn't affected in such view.
We cannot make up our mind to believe such in/output structure only, however, in practical meaning, they might not make any of the contradiction on surface.

However, the existence of #f causes such optimized structure excludes some series of the f causes to make some good existed invariant causes bad non exist invariant. We cannot understand this in mathematical way. It's collision of uniqueness of the whole, so it's outside of them.

# General Tips BB
We understood the observation needs the calculation order O(n^6) or so, however, only to collide the uniqueness of the whole, we only need O(n/lg(alpha)) calculation order. This is to stand the viewpoint on high layer and low layer on each block, then, randomly (or another words, completely depends on the data stream) switches them with breaking dimension barrier causes the viewpoint switches some another space. We don't have the language why they are inhibited yet, however, it's non deterministic ones in theoretical about the pigeon hole.

# General Tips BC
The compress/decompress is the analogy to categorizing the input.
This is: exists some x, Ax==[0, y] categorization causes only 1 variable with the index of nonzero row.

So (de)?compress is the result they learns some of the habit of some of the ring or N, then, take some index and input one variable.

So in their meaning, taking N as first variable domain causes prime factoring concerns.
Then, prime factor matrix F concerns some of the {0,1}^n=={0,1}^(p_0^e_0...) ones, they causes function countup with some of the observation theirselves.
The prime factor also has some of the internal structures they stands, so some of the small number will be fixed, however, I don't know whether large numbers also them, however, prime factor can be created by some smaller hierarchy F_(p_m_k) calculation with F_n calculation with i-unit on F_p.

# General Tips BD
We regard any of the data as constraints if they're used with some of the context.
So if {aleph_omega, in/out surface, #f} concerns some of the data (middle of them looks like so), the general optimization problem (they're not actual general, however, we can form them into the one if the problem isn't deviate from some of the convergences) obj. \<Qx,x\> s.t. Ax\<=b ., if we rewrite them into invariant problem, the fixed constraint might from the objective function and whole constraints, since we can write down SAT or some combination with constraint problems into them includes some series of the logics and arithmetics, we can impose the correctness of the middle equation into the fixed constraints. However, the fixed constraint index is obscure with some of the condition they're fixed in real world problems.

So if fixation order of the invariant has multiple meaning, the N has inconsistent part if we start with opt.problem with some sort of the intent they causes constraints treated in R^(n\*m), however they're natual after they're fixed for same world also includes us.
So the condition might come from lack or carry of the constraints the entity cannot stand, and the theoretical meaning search is the way we understand but not in the first order theory if they're broken in such way. So they might, {}-\>N-\>R-\>R^n-\>R^(n\*m)-\>opt\>N/(m)(inconsistent)-\>R(inconsistent) order, we bet.

However, if such order is truth, we cannot make rigorous distinction on N and N(inconsistent) without some of the type system or so.
Since we have ZF(C?) with dimension/cardinal barrier, we can bet the consistent structure if we doesn't deviate from them because of optimize problem's numbers' order of the magnitude relationships in first order, this is to bet first order logics and second of them(, first order arithmatic) consistent in possible wide ranges they can cover.

cf. However, to stand the observation is correct stands, the consistency also collaterize our believes on consistency on {}-start combinations.

cf. Heat pretends to like as much many intent as possible to appear in instance of real forms in nature. (However, huge much of the heat doesn't continues enough time length.)

cf. Some sort of the intent uses variational method to form with, this is compatible if the constraint slides.

cf. However, many groups of ongoing mainstream physicist favoures to excludes variational method so to analyse their strict structures as possible details.

# General Tips BE
Tips BD's n-th order inconsistency could get any of the intended result as a phenomen on the space they live because arithmatic paths slides.

So the matter is, our space is {}-start consistent space or not, in another words, the arithmatic operation doesn't have multiple paths possible with after optimization has done.
However, to start with observation is correct stands, the intent we learned first changes the shape of the #f countup glitches on factor concerns.

A #f and factor collaterize each other on somewhat on f-recursive, to show they're only one such structure or not on our space is to solve some of the optimization problem with some non-normal arithmatic-like operations on somewhat optimization problem.

This is to write down possible N/(m)-valued optimization problem as possible logic-like systems if they're observable from our space on the correspondences but they're huge enough.

# General Tips BF
To check 4=2\*2 glitch, we can write down {1,2}-input 3-bit x 5 block on the half and extra of the function to code, then, -=1 each bit causes 2-bit x 5 block, whole of them is 10+4+1 bit however function itself has 16 patterns.

This can be {0,1}^14 cup {i,j}^2 on #f countup : some different parts with only to code {}-start structures.

However, stands on our experiences, this could become false description on the system when they're observed by some existences.

# General Tips BG
If whole condition can be the condition we can write down with the uniqueness on the whole on possible outside of the description with {N,R,f}, this condition especially includes mutually support each other some of the existence and one of them with {N,R,f} or their root, the condition can be written down into such Ax\<=b condition with some of the (non-)linear objective function.

So the observation condition we call is, to make them into invariant problem and fix the edge with some of the indices on A.row, on some of the stage, they can have parallel (but not the same) condition on the originals.
If some index chain of the condition has some of the meanings, the observation can change the internal constraint structure meaning on the arithmatic basis.

We can write down such condition with dimension/cardinal barrier mixing they causes \> 2^2^X order with set X.

We don't have any of the clue the subject nor object can slips on such condition or not but, we can do calculation such of them. (At least such of the context.)

# General Tips BH
However, with the tips above, making binary tree of the function on some system concerns phenomenon is the most important part if we understand them.

This is because binary operator theirselves aren't slip on the variable to variable, also if we gather them as the method with better manner on some of the barrier can exclude such \> 2^2^X phenomenon on the occasion.

Either, without such binary tree, we cannot decompose some of the problem in the safe way. This is because triplet tree can have 4 variables on invariant, such of them causes invariant counting glitch, so we have slipped occasions on some of the existances in such way.

# General Tips BI (Retry on General Tips R)
So we retry general tips R with the information we have now.

(i)   It's the access to another status in the internal of the world via optimization around the calculation.
(ii)  They breaks N basis. The N we has a glitch via the context subject have.
(iii) It's no problem. Any of the data has the information amount upper limit on the meaning of compression and they doesn't make consistency glitch but it's weired by the view of ours.
(iv)  The description on such system we have is not enough for now.

We can test the hypothesis by doing real compression/decompression algorithms.
However, doing such test can be a glitch viewing from some administrative existances if (i) is the correct and there's some of the access control glitch, we afraid such existance counter measure if they exists, so we're locked.

(iii) seems not to be the truth because we can think about any of the function on f such #f glitch.

(ii) can be included into (i) case. This is because we get/put the calculation result real entity data, if the serial stream compression/decompress doesn't have a glitch, this might be true.

However, (iv) case is the most nearest to the truth we think.

# General Tips BJ
Around tips BI (iv), the description form 0==det\[\[f_(0,0)(x), ...\],...,\[..., f(n-1,n-1)(x)\]\] has some another description form they includes hidden status for subject as treating well.

The form describes: each fixed x=x_k, the base geometry on each relation described by Integration form for good continuous ones. Also, x transision includes the subject internal status transision.
The form might has the relation f_(k,0)==\partial^k f_0/\partial x^k.

However, this is one of the possible form outside of the optimization. So we don't have any clue on another forms.

# General Tips BK
Checking function to BF, first part can be checked by:
with a_k . b_k c_k form coefficients,
f_0\_\*  == Sum(a_k + b_k / 2 + c_k / 4)
f_1_i   == f_0\_\* + a_i + b_i / 2 + c_i / 4
f_2_i_j == f_1_i  + a_j + b_j / 2 + c_j / 4

with matrix form:
\[f_0\_\*, f_1_0, ..., f_1_3, f_2_0_1, ..., f_2_2_3\] ==
\[\[1 ... 1/4\], ..., \[1, ..., 1/4\]\] \[a_0 ... c_4\] (first digit)

dim(left part)  == 1 + 4 + 3 + 2 + 1 == 11
dim(right part) == 5 \* 3 == 15
rank(matrix) == max.

So the matter is they have a integer solution or not, and we have them with first digit if large enough F_p.

Either, we can control first digit on {b,c}_4 and Sum_k=0^k=3 {b,c}_k as to be 0 or 1.


the second part is checked by:
Sum_k=0^k=3 a_k . b_k c_k {1, 2} -= Sum_k=0^k=3 a_k . b_k c_k,
a_4 . b_4 c_4 += Sum_k=0^k=3 a_k . b_k c_k.

first part condition, c_k isn't needed up to 2 term.


We can check whole calculation up to 1024 patterns, truth table has ~ 2^5 / 2 patterns.
The function pattern is up to 2^3\*2\*3 + 2^2\*4 + 2 == 66 parts patterns for each bit countup.

# General Tips BL
So below tips BK counting up some weired.
However, to find invariant on first digit on \[f_0 ...\] == A ((a_k+b_k/2)) causes the problem with balancing s.t. A^-1 \[f_0 ...\] == \[((2\*a_k+b_k)), 0\] mod 4.
the 0 part is first digit meaning in former one, so large enough variable bits causes tan\<a,x\> type invariant.
Since we don't have better treating tools for now for first digit matrix operators, this is the view we think weired ones.

So, balancing some in/output for f meaning, nor, optimizing functions from data, nor some learning method, nor, ourself viewed from multiple layer perceptron could have such limitation.

So finding some of the regularity on dataset causes dimension decrease causes some of the observation we think.

# General Tips BM
In addition to tips BJ, also with tips BL, the observation seems to seek internal states some of the another places if we stands outside of the calculation subject.

The optimization method causes continuous on internal states on tips BJ if the constraint chain isn't change the fixing equations. If they slips to another combination on fix, internal states some of the element can have uncocntinuous internal states.

We continue to investigate what form to describe them better with we can have.

Nor, we should reserach such tips BL's vector to be invariant for given input.

# General Tips BN
Talked with gemini, we got the result of the root description of the description as:

{descriptionability} -\>
    {{descriptionability, information or energy, reference to initial value and their result heat}, combination},
    {{descriptionability, the existance of higher structure, the existance of another one}, existance of the one},
    {{descriptionability, multiple viewpoint, single viewpoint}, N},
    {the existance that we cannot describe}

However, we cannot consider this is max rank or whether there exists another description root or not now.

We and gemini concludes tips BN description can be change and someday it's able to become ancient.

# General Tips BO
With tips BN, the observation case is somewhat reference to initial value and their result heat, or, from higher structure, or, from multiple viewpoint, or, the things we cannot describe.

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU
* https://osdn.net/projects/bitsofcotton-randtools/

# Refresh Archived
This repository is archived, so without bugreport, will no change. 2021/02/09 version is archived. It's ok. 2021/02/15 version is ok for retest. 2021/02/17 recheck ok, sleeping, 2021/02/24 sleep 2, 2021/02/07 sleep3, 2021/04/10 sleep4, 2021/04/20 sleep 5, 2021/05/14 sleep 6, bug report is welcomed.  2021/08/29 recheck ok. sleeping. 2022/09/14 recheck retry sin, cos taylor op. sleeping 2. 2022/12/26 fix one of the glitch concern with integ/diff. sleeping 3. 2023/04/10 add Tips H. 2023/05/06 add Tips J. 2023/06/16 add to Tips N, O. 2023/06/17 add Tips P. 2023/06/18 add Tips Q. 2023/06/23 add Tips R (iv), S, T. 2023/06/27 add Tips U. 2023/07/10 add Tips V, W. 2023/07/11 add tips X. 2023/07/18 add tips Y. 2023/08/07 add tips Z, AA. 2023/08/14 add tips AB. 2023/08/16 add tips AC. 2023/08/27 add tips AD. 2023/09/03 add tips AE. 2023/09/05 fix tips AE, add tips AF, AG, AH. 2023/09/06 add tips AI. 2023/09/09 add tips AJ, fix below/above in AI. 2023/09/11 add tips AK. 2023/10/03 add tips AL. 2023/10/08-09 add tips AM, AN, AO. 2023/10/09 recheck, so higher digit is broken. corrected. add tips AP. 2023/10/14 add tips AQ, AR. 2023/11/02 add tips AS, AT, fix tips AT. 2023/11/07 add tips AU. 2023/12/01 add tips AV. 2023/12/02 add tips AW, AX, AY. 2023/12/02 extend tips AY, add tips AZ. <strike>2013</strike>2023/12/02 add tips BA. 2023/12/04 extend tips BA, add tips BB. 2024/01/10 add tips BC. 2024/01/17 add tips BD, BE, BF. 2024/01/25 add tips BG. 2024/02/03 add tips BH. 2024/02/04 add tips BI. 2024/02/06 add tips BJ. 2024/02/08 add tips BK. 2024/02/09 add tips BL, BM. 2024/02/29 add tips BN, BO.

