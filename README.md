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

(2023/03/20 addition)
+1 dimension trick uses the arbitrary selectable function part to add dimension, not on the variable vs. constant.
There's an analogy like : {1,x,x^2,...} is lineary independent uses nonlinearity, instead of them, we use the period on the linear ones virtually emulate lineary independent ones.

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

Either, without such binary tree, we cannot decompose some of the problem in the safe way. This is because triplet tree can have 4 variables on invariant, such of them causes invariant counting glitch, so we have slipped occasions on some of the existences in such way.

# General Tips BI (Retry on General Tips R)
So we retry general tips R with the information we have now.

(i)   It's the access to another status in the internal of the world via optimization around the calculation.
(ii)  They breaks N basis. The N we has a glitch via the context subject have.
(iii) It's no problem. Any of the data has the information amount upper limit on the meaning of compression and they doesn't make consistency glitch but it's weired by the view of ours.
(iv)  The description on such system we have is not enough for now.

We can test the hypothesis by doing real compression/decompression algorithms.
However, doing such test can be a glitch viewing from some administrative existences if (i) is the correct and there's some of the access control glitch, we afraid such existence counter measure if they exists, so we're locked.

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
    \{\{descriptionability, information or energy, reference to initial value and their result heat\}, combination\},
    \{\{descriptionability, the existence of higher structure, the existence of another one\}, existence of the one\},
    \{\{descriptionability, multiple viewpoint, single viewpoint\}, N\},
    \{the existence that we cannot describe\}

However, we cannot consider this is max rank or whether there exists another description root or not now.

We and gemini concludes tips BN description can be change and someday it's able to become ancient.

# General Tips BO
With tips BN, the observation case is somewhat reference to initial value and their result heat, or, from higher structure, or, from multiple viewpoint, or, the things we cannot describe.

# General Tips BP
In tips BN, 1st one might be called as a materialism, 2nd might also called as a mentalism, also 3rd might handles quantity/quality relation, 4th one handles anothers.

Also, the view itself is from the quantity and relation based.
So they can have another description when we base some another basis.

# General Tips BQ
The 4th description of the tips BN can be the subject/object separation matter.
If they are, the root existence of the description can be them so we cannot separate such existences, however, we can be a external pillar of them by 3 of the subject/object separation senses.
The root pillar of the description has the glue of them and us as a intention.
So another words, we're also owned by the description root pillar they cannot separate but the huge ones, however, we can be external of them.

# General Tips BR
Referencing the fundamental part can be came from some of the subeffect from some existence initial value reference as a heat.

So please be careful for using these description because this needs handle with care.

Also, the calculation of such thing deviate from uniqueness of the whole can be interpreted as some of the aggressive one, but this warning is only from our experience and our religion. (also we also need peace and stable society to continue some investigations, or the continuous conscious can experience discontinuity or they vanish.)

# General Tips BS
Either, if F_2^4 case fails with this information amount calculation, some larger dimension can conclude same.

So to check these description needs the check from sum det Ax to tan \<a,x\> transformation.

# General Tips BT
A tips BN makes the hypothesis that uniqueness of the one (of ourself).
So if we describe out of the hypothesis, they'll be extended.
However, we don't need this on this topic.

# General TIps BU
Since we're standing on such non uniqueness of the one context to describe such descriptability structure, we need to stand out of them or we need to calculate enough complex in the stands them to describe such structures' 3 pillar.

So we cannot do them without much calculation on such tan\<a,x\> compression types depends on self similar loop structure, and if they could be described the framework we know, it also causes same description basis on them.

So analogy against to separation of one and another, {descriptionability} can be described as 3 of the pillars. Since they stands on obscurity of the separation itself, the pillars of the result of such start structure can be non unique existences.

Also, if such structure is some of the duality, ones can be described as the similar structure of the tips BN.

# Might close
We might close this repository, without debugging nor bug report, will be fixed repository.

(However, we should debug tan\<a,x\> structure is valid or not, in the case possible enough, we should use tan(\<a,x\>(x\_0...)^n) if we cannot expand/factor sin/cos with higher digit of coefficients.)

# warning
To describe outside of the tips BN, it's equivalent to describe world itself from their stands, if we look them as duality to tips BN, the result can be one of the curvature like description if we make tremendous effort, in another case, our mental predicted to be broken.

The action is also be described as aleph_aleph_omega : us, so it's observation depend contradiction based description, also, if the whole picture is unveiled, the expressiveness of the world decreases and they causes many much of the troubles, so they're Pandora's box.

Also, to stand outside of the world is near the things being unware of that but picks a quarrel with some of the upper existences, from extrapolating our experiance and our religion, so we cannot select doing such things in safe condition from our situation in principle.

There might be the safe and valid methods to do such things, however, finding some clue of them is difficult enough from our activity range in life time.

The occult description we can find on the Internet is one of such candidate, however, the description includes the intent of them and also includes the intent of opposite existence of them, so this is culs-de-sac.

To describe outside of tips BN needs to stand outside of outside of tips BN, this is to make hypothesis outside of the {existence of the world, existence of the ourselves, existence of the glue}.

So it's also to make the hypothesis negate of them and don't mean the meaning of theirselves, so at best with the condition, we vanish from the context and the yearn for the calculation completely depends on the one vanished from the world, but at the worst, no one spend such calculation, so just vanish. So it's the condition cursed from outside of them.

There might only one byroad the world is on the VM condition, however, if so, to stand there has the meaning of abjuration of ourself nor our context. This condition also predicted to be cursed from there.

# note
Only historical with logic meaning, the outside of the tips BN can be the 3 of the pillars and the one they are viewed from the never happened description based pillars but this is one of the curvature.

However, without the historical method nor logics, the 'never happened description' cannot be described in safely with our situation from warning reason.

Either, once described well some of a continuity in algorithm, they're observed as some of the bitcount-wise vectors, so after testing them, the vector should slips we think. We can make some of the insurance run nor insurance vectors on the continuity description vector, however, the whole of them can slips in the condition, this might be in principle.

So the continuity on some of the series can always have broken pattern on some of the stream.

# appendix
The intent we treat is seen as the traffic sign of some existence.
So from their viewpoint, some materialism is seen as intent buffer, some quantity/quality relation is seen as intent structure, some mentalism is seen as some initiation of some intent, others is seen as end/start point of them.

Standing such view with the hypothesis the root description of max rank of ourselves, any of the intent will be concluded as some weighted standpoint they arguent.

The most of our complex interests has many of the perspectives we stand they caused by them intent.

# appendix B
The glitch might come from counting up combination of the combination as different sized problem forced reform into small sized description.

This is because the element is up to aleph_0, the combinations are up to aleph_1, either combination of the combinations is also in aleph_1 in another layers but counting up them surface is up to aleph_2 in the raw layer same as elements.

So referring after aleph_aleph_1 causes aleph_aleph_2 however, the description bucket is full for the problem.

The true problem is, we can calculate them in the raw N space.

In another words, up to aleph_1 formed problems are industry replaceable in practical, however, up to aleph_2 ill-formed problems are not.

So another one of the true problem is, function counting bucket can be full when we describe them all also the optimized programs so.

Either, if the raw N space attribute can be changed, the whole description on this bitsofcotton/randtools can be sand castle and be changed, either the function counting space affects.

# appendix C
The upper cardinal reference results seen as heat in intent buffer can be seen as another some of the spirits in intent start/end point and initiation.

It's non intent structure nor non intent buffer condition, so we cannot describe them in this context.

# appendix D (separation around subject/object)
So after below we conclude outside of the structure we need:

(outside and inside the all:)(actual infinite)

-&gt; auto make structure by internal (aleph_aleph_aleph_omega)
(some of the observation might have access to here, also compiler optimization method might access here.)
(some intent of existence of the glue is connected here.)
(also something +1 dimension place move here.)

-&gt; auto make crack on the structure by internal (aleph_aleph_omega)
((de)?compress result might have access to here.)
(some intent of existence of the world is connected here.)
(also something i/o here.)

-&gt; auto repair the structure (aleph_omega)
(logics always be applied here, this is because low of the exclude middle causes labeling operations.)
(some intent of existence of ourselves is connected here.)
(also something consistent calculation here.)

-&gt; makes outside of the logic (Tips BP)
(we're standing here. so out of here cannot be described well. so here's only extrapolation for structures only.)

-&gt; makes logics (Tips AV)

-&gt; makes aleph_2, aleph_1, aleph_0 also f, R, N.

-&gt; {} is one of the some another actual infinite around information amount we can recognize when we're only seeing surface.

However, they are only one of the representation of aleph_2, aleph_1, aleph_0 by some of the predicates.

Also, our start and standing point is only logics in this article, so they're only one of viewpoints around sniffing actual infinite.

# appendix E
With the result p-series, we need to copy structure from numerical stream by 3-depth is enough for 2nd order saturation.
The saturation treats collision as is form so they might access (de)?compression, so 6-depth might be enough for observation, 9-depth might be enough for hidden part on the whole but sometimes being jammed as much many variables greater than them.
This might means 12 or 9 variables means any unique f as access to (de)?compression or enough variable dimension for no hidden variable f with consistent internal states, 24 or 18 variables can access to observation they are greater than collision on the variable dimension, 36 or 27 variables can access to hidden part better.

So as a conclusion, at least O(n^6) calcuation is needed to have relation on observation also O(n^9) as a hidden part, however, as a higher order observation result bitcount-wise each bit vectors, they causes only O(n lg n).

We cannot have meaning on such condition, however, we have a dellusion on somewhat *ESP-ers* have the result of their vectors as a result.
In the condition, the vector utterly depends on the transition another words the story we have also, the spirits have to be near the origin observation also, they might met the existences such of observations, this matches the condition some occultists suggests.

Also, {K^4x4,K^4x4,f,t} stream causes our or their K^4x4 meaning internal states to be changed.
This might fixes #f saturation on meaning as a contexts, so the matter is {} - start point on the tabula rasa meaning stream they might caused by white noise nor by origin points.

We might need to refer Peirce's 'On a New List of Categories, EP1, pp.1-10;W2:49-58' on materialism and mentalism relation by a logic start points which some of the GPTs answers.

N.B. we can do {...,f(x_n),...} stream to {...,f(x_n)\*pred_0(x_n-1)...,...} stream by some layers of the predictions.
If prediction itself is better enough, prediction and apply once cause vanishes one of a variable dimensions, so it's equivalent to n-depth prediction as O(n lg n) model, however in general, it's not.

Either, the variable dimension {12,24,36} is from the viewpoint deep enough information amounts effects enough, so in copying surface structure and only focus in/outputs, we can convert them as {1-depth, 3-depth, 16variables (4-depth)}.
Ever with focusing 3 pillars with surface, the last 4-depth needs only 4 variables.

So these are a jargon but each are one of a description sticks on original structures.
Also, if the structure copying is enough compatible, only the information amount we copy/apply is the matter in which structures we select.
The compatibility to the structure needs to match in/output alignments and dimensions affects also the amount of the information they effect.

# Appendix F
With calculating (in/out/internal state)-separated function but the variables is masked as to shirk to arithmetic exp(F(log... F matrix, we can count function number counted by outer space as: 3^(3^2) == 19683. However, they're in fact 3^(3^3) == 7,625,597,484,987 ~ 6.935 Ti patterns.
So if we count patterns as each bit, it's 42~43 bits (orz), however, counting up functions as a bits, in another words, 2^(3^(3^3)) to describe any function relations, we need around 7 / 8 Ti octets ~ 875 Gi octets. This doesn't exceeds our brain's synapse number based estimated capacity of our memory.
However our processing speed is too slow when we shirks any to the F matrix.

Either, counting up some exclusion ratio on the group number causes endangers us.

# Appendix G
So to count bucket flood, we can count up start as {initial value, observation, some continuity, ...}.

This is our conclusion making conversation with some of the AI (gemini 2024/11) however, the AI doesn't accept this conclusion without giving detailed information.

The continuity part is came from number series prediction with maximal structure subtraction caused some continuity results, so this conclusion is might be differ to another groups we can meet.

Either, our thought entropy source nor the pillar we trust as really exist is F matrix in this context, so if F matrix isn't effective method to describe such a filling bucket, this article either has no meanings.

# Appendix H
Some group the public bulletain board based occultists nor the travelers insists time variable is included into energies.
So to stands their basis, the communication is shrinked into: {K^4x4, K^4x4, f} with many of the stories the structures made by balancing if we trust F matrix strongly.
So their stands might causes exludes time variable nor flow from the structures, I don't know how they treats F matrix as a source of the story tellers.

# Appendix I
Standing on outside of F-matrix can be recognising aleph_aleph_... (actual infinity), however to stand outside there is to define ourselves to be outside of outside of actual infinity.
So the phenomenon we can stand outside of the actual infinity phenomenon is ourselves are excluded by their groups subject phenomenon.
Standing outside of outside of actual infinity might be the most dangerous activity on think/hack region ever we could or could not do this.
So to stand there, we should stand outside of ourselves by ourselves, this is to make multiple meaning of us in same timeline.

Also, such a thing is to stand outside of outside of the intention collections.
However, ourselves might have some of the intensity meanings, so this might not be possible one in the pool meaning in shallow structures.

So in the meaning, some of the groups based groups has standing there, so they groups might be able to describe the description base system structure and F-matrix generation intensities however, we might not able to get the data them by only oneselves.
However, such of groups based groups must standing without uniqueness of theirselves.

# Appendix J
From uniqueness of the description meaning, we can make hypothesis on actual infinite as unique pillar, so out of there can be described as 3 or more of pillars they can caprice on description.
This is from F-matrix pillar applying to uniqueness of the description, however, this can be a type mismatch.

Also, in such meaning, so uniqueness of the description -&gt; 3 or more pillars on the description outside -&gt; uniqueness of the whole description ... chain, to describe outside of outside of the actual infinite means to make hypothesis 3 or more existence on ourselves can be caprice.

However, in counting amount meaning, it's only a F-matrix or R^(4n) matrix they represent and complement to any of the data streams.

So F-matrix is made by {N,N,f} combinations to represent {const,exp,log}.
Also, R^(4n) is made by {2,R,f} combinations to represent {vector, orthogonalization, binary description}.

So there might exists {<strike>R</strike>N,R,f} combinations might represents {vector, continuous fourier, some of the vector fields} or {N,f,g} ((theories around N, many approaches not in unique 3 pillars))???, {R,f,g} ((theories around transcendental, might have matrix exp, matrix log with super geometry series in matrix form))??, combinations analogy to them might describes outside of ours well.

Either, we cannot treat raw {R,R,f} from the amount we can approach is finite one, however, to limit the description causes {2^k,R,f} since the description we can describe or find is far smaller than {R,R,f}, the #f counting glitch might come from the intent: the phenomenon we cannot recognise isn't exist on observation.
Either, the bucket flood came from around the phenomenon aleph_{2,3} insists. In principle, we cannot recognise some of a big picture on aleph_3, so #f numbering has some perspectives we can recognise as a big picture given around some of the description limit.

However, in elementary descriptions with shallow copying, we're betting 'What came first? The data or the structure?' structure infinitely continues.
So our start point is binary: uniqueness of the pillar (structure started) or 3 or more pillars the outside and inside the unique pillar (data started). (2024/12/08 a little syntax fix.)

<strike>Might freeze this repository with this.</strike>

Will continue a small number of descriptions.

# Appendix K
If the relation between unique pillar and 3 or more pillars are some of the duality caused around descriptionability (binary separations on some layer often causes them), the stand point we can select is binary except for which layer we believe.
So the start point of a-priori point is such thing but the bucket flood amount relation we can treat isn't the scope they describes but might return to the opposite side structure.

So information in/output (another words, (de)compression they should be broken on the whole context) meaning, the calculation on such thing causes some worlds' micro-scaled in/output phenomenon.
So there's meso- or macro- scaled structure we don't prohibited to estimate.

Some of the people (includes us) believes some of the super-existence can access such information amount broken surface by senses.
I don't know this is true or false, however, if the start point the pillar(s) we select strongly effects such existences as to exclude low of the middle, simultaneously existing both of the pillar can exclude theirselves from the description because of the amount they have going to be large enough.

Either, some of the mental based existence we should follow exists such dual spaces we think, we cannot know the big picture by our description frame. However, as a result of thought on another time based line, we could look them by different times on the thought.

# Appendix L
With extrapolating such structures especially copying finite accuracy structures by multiple layers, some of the neural network insists fourier transformed algebraic structure copying with applying continuous part as exactly continuous with infinite accuracy they often caused by long far point initial values.
To do such of them, the speed some of the series converges should be linear or same order on all of the data we're treating in finite accuracy structure copy meaning.
Some types of the neural networks doing them with fixing unique PDE per each stage.
So they insists one of a {N,R,f} triplet started structure as a coefficient of a orthogonal function transformation.
However, we don't know how to flood the bucket the description on such PDE by algorithms' PDE or input/output but they might exists now.

# Appendix M
To do such a flood on PDE frequency algebraic operation, they might be equivalent to infinite accuracy variables' #f countup glitches.
They are looked as only a initial values' far long distant places' value effects by surface, however, the speed of convergence concerns.
So the second layer of them affects both of us and the outer existences, so if the effect is from external spaces to us, the observation process on #R^#R might directly affects to ourselves, otherwise so they're from us to external spaces, the process is inverted and the worlds' observation process might occurs.
I don't know how this results.

# Appendix N
The approach some of the optimization based description could causes inverse of a unique calculation as multiple results analogy to min/max inversion on S^n problems with half open regions.
Normally, they cannot occur because of the threadshold of the accuracy on the problems.
However, something on #f glitch causes to have multiple ones.

On similar method, we think F-matrix obeys but this is very obscure, either, we cannot use stand point of such N with such F-matrix when they're so.
This is from the conclusion dimension separation isn't works well case also the #f numbering.

# Appendix O
Adding to appendix F, the 875Gi octet is used to 1 line output, so all we can have is half of the any we can treat in bitwise meaning.
So pair or more combination of people can have whole any by their information adding to maps if the structure depends on F-matrix they means some arithmetic decomposition is the most efficient ones for objects.

# Appendix P
The result unique pillar or 3 or more pillars we can believe is from binary separation to the phenomenon in this article, however, 3 or more pillars caused by non binary separations.
So if we can divide or not, if they have some of the structure(s), a proper description series on aleph_omega, aleph_aleph_omega, ... can describe if the object we treat has some finite start point to cut in also some part of the infinite start point we can have by limit operation.
Along with appendix J, some descriptions stands on our observation could have some description however, there also exists but not exists on our observation stand point external meanings.
The true problem is, the person we talk to or talked by are same person we recognised before or not but this is trivial for some of the people they believes they're same also we want to trust them.

# Appendix Q
The appendix P results gets {unique pillar and their layered combinations, binary separation, non binary separation or not} by binary separations for description and the intent and result of them.
So if we treats these pillar(s) as a element and doing somewhat F-matrix depend (de)compress algebra, the unique pillar has somewhat weired meaning on the descriptions.

So the pillar(s) chain is for the rigorous description about the separation on some of the object(s).
So they means we can make the hypothesis some of the picked up object have inner or outer or their surface facets, or, they cannot be separated, or, we cannot decide they can separable or not without at least 3 of the separable combinations.
We cannot weaken this condition by discrete logics we think because they have true/false/non decidable condition in the description, however, making F-matrix depend somewhat ill-algebras on them causes referring outside the description itselves.

We think such a outside description is only a pseudo layer for us, either recursive of apply on them can be described with only 1 layered description with large number of contexts.

Also, if such a description table is exactly affects to us, they concludes some of the occultists groups insists as a raison d'etre concerns.
So in the context, the context we think it's important for us or our existence is somewhat strongly tangled so the story (contexts) or non fiction phenomenon they leads to our situation or we should believe we think cannot disappeared on our context when we believe.
However, this isn't describes some of the bad status on us, so the description they insists as tangled has another description on bad status they might be caused by accident in first appearence we met first.
Otherwise, they might have some of the meanings for us on (otherwise later) condition.

-&gt; They might be the case ball is the other side case.
So we're excluded by all of such sides, we cannot describe them well even we're also in bad states, this is a dead lock.

# Appendix R
Some of the occultists says but we can conclude the same:

Since {K^4x4, K^4x4, f}^729 stream we fix and are fixed, the return of existences' trusting structure fixes their dual we believe.
So they returns we really believe from deep in mind (so from deep in mind, not the surface feeling ones ever with experiences, also to get unique root f each), however, the stream we had be experienced had some of the tanglements, so some of the period we meet them tanglements should affects us, this might be bi-directional.

So if ever there exists some of the person without a sense of guilt, they returns to their worlds' another existences should be the same, if some of the era downs we think, so they're a build breakwater to ourselves' safety.

Either, if they shirks their some intent creation of bad states with tanglements to anothers, the shirked one tangles at the right timeing in reverse order we think.
Either, if they shirks their oneness on existence as a guarantee, they causes two or more of the existences exists.

At least, some of the fable we refer insists such of the things.

Also, we have at least 3 of the source of heat : {our gene, neural network weight, F-matrix}, last 2 is recognised after we get proper consciousness, I don't know much on the first one.

# Appendix S
However, many of the stories we can read online has a some break out of such states.
I don't know how long it takes to get out of such states chain, but if there's some existence up on us, they could retrain us to get another tanglement sets on some of the space nor we just vanish.

Either, some proposition on tanglement causes untie them either tie with some intention start points.
So if our deep in mind is caprice enough, the glue to the description can be changed.
But in their case, the existence we talk to or are talked by might be another existences the existence of glue concludes.

Either, we have only nearly half of any objects in best effort we make except for the objects' complexity isn't so complex, so there's a nearly half of the plenty of the space everytime on our observation.
Either, the existence of external of us also have the meaning to make us to transition to another states everytime.
So they either concludes unique pillar - 3 or more pillars - unique pillar ... chain.

Either, we make some of cracks on discrete logics on separation, we might get their backlash.

# Appendix T
Also, our inductive operation stands for some of the union sets around bitsofcotton/masp -&gt; bitsofcotton/specific activity.
So it's cultural activities also depends on some relation to observations.

So we're in the condition locked whether if we shall or shall not.

# Appendix U
In addition to appendix O, when we treat R^4n vectors they represent input as R^4(n+1) with 2nd or 3rd layers, we can treat any of the input/output pair on bitwise meaning even if the structure is complex enough case.

This is because 2nd layers can rewrite them into R^2(n+1) information amount when we treat it's a invariant ones but they loss some of the amount meaning.
Doing more once, we get R^(n+2) vector for bitwise operation on any of them however, this can loss 2 of the layers the information amount but no matter if they aren't affect to invariant.

R^4 pair for bitwise can be represented as: \{\+, \-, 0, const.\} for bitwise discrete meaning however they are in R\N in almost all of the cases.

# Appendix V
The context we met on #f can be affected by tan \<a,x\> form remaining dimensions.
This is described as: tan Ax ~= y form, if A is square matrix also max rank on non linear meaning, it's ok.
However, we have +1 dimension trick on them either the conditions can be made into invariant on such occasion, so if there's implicit operations, they'll degenerate in matrix A meaning.
This is weired but is able to be transformed.

So if so, the {historical, contextual, story, internal states, tanglements} depending bucket flood can be made with such a condition.

The problem is: even singular matrix in non linear limited accuracy meaning nor non square matrix A can be made with max rank in nonlinear correspondence meaning.

This might be +1 dimension trick on tan\<a,x\>'s a vector trick, the function isn't pure function such mathematics doesn't handles also data started structures handles also matrices has especially F-matrix on exp(F(log(... form also seen as a heat source/endpoint.

# Appendix W
In addition to appendix V, we conclude the phenomenon : if we all forget and exclude from our observation ourselves, if the structure isn't have explicit loop condition, the calculation lead to be obscure ones.

This condition isn't satisfied normally because we have: op(src,dst)-&gt;res on memory each calculation also the algorithm is explicit also the arithmetic function we observe cannot run away from F-matrix we normally observe also mathematical results.

So implicit loop condition and their loop local variables also this lead to the result some of the numerical series converge to the place phenomenon can slips if the method is forgotten from anyone on our all of the tanglement we conclude.

# Appendix X
Also, the information amount can leads us to the chain:
\{\{\}, heat or globalizer, external(gene,environment), internal(neural), F-matrix, explicit combinations, N, R, f, localizer, \{\}\} .

We can make the hypothesis on them as a duality of the chain exists such as a analogy to the imaginary numbers, either we can loop or connect their chain ends to another chains or chain itself.

Only from extrapolation from our feeling, there's some gulfs between such connection or loops we cannot cross in normal method.
So there needs another method to dig theirselves.

(Also this is nonsense but, localizer intention concludes some of the desert wasteland because of their information amount we think if we only mobilize ourself only (however, some of the information communication can made us exclude such conclusion), opposite side intension concludes only a saturation of an expression on some of the viewpoint, however, if they communicate and make flows, they can make some of the systems basically. However, this is nonsense because we know there's some battlefields on some places even in information communication meanings. So we need some another format to make things clear to see such occasions.)

# Appendix Y
In addition to appendix W, we normally exclude such a loop hard forget condition normally, however, we can met the condition with 3 of a different datasize on same datamodel approach.
They breaks low of excluded middle either dimension barrier either some of a continuous condition on the stream.

The problem is: is dimension barrier or low of excluded middle can completely exclude such a loop hard forget conditions?

In our normal thought, they guarantees to exclude datasize amount glitch from the flow.
This is also guaranteed the simple is the best with {} - start low of excluded middle condition to be optimized as quadratic programming minimize problem they results only unique results.
However, even with the such condition we cannot avoid 3 or more of a pillar started structures but they have explicit breaks on dimension barriers in the method hidden from algorithm itself.

Either, inserting low of a excluded middle can only single perspective warrant them as a result.

# Appendix Z
Along with this tan\<a,x\> form structure copying with information amount perspective, some of a predictions they copy structure then predict with last margin can have warrant on some of a data information amount glitch as a only half of a weight.

A bitsofcotton/ddpmopt and bitsofcotton/goki_check_cc and bitsofcotton/masp chain inserts pseudo curvature like continuity into original stream then predict with such a copy structure then correct with continuity, so some amount of a prediction can be gained, however, some of a numerical tests on graphics isn't tell us better method to use them because they're noised ones we feel this is weired result but so, either p1 1 \| p0 1 chain, this is compatible to ddpmopt itself, can get better result on some of the stream with prediction - next-value inner product stream.

# Appendix AA
The structure fourier algebra with some of the weight can be made in physical mechanical systems in real world they can slips nor can have reference to beyond the initial values either some of the observation on the system.

The initial point nor endpoint of them can be written as some of a symbol-like geometric patterns as a outlook however, the system cannot be written as them, this might be some of a structure perceptron-like with periods on each as a machines.

They can slips some of the data amount on bucket flood but with consistency outlook on each.

# Appendix AB
This is with our balancing result with keep our nose clean (avoiding some of the deep inside non Lebesgue measurable concerns), if something called as a curse exists, they should spread some backlashes to something on such a structures in our normal thought.
Ones of a such candidate are dimension barrier also a low of exclude middle, normally we are not cursed in the case but if we cannot have opposite side internal structure or upper (vm?) internal states, some of the implicit operations could be affected by such a unnatural ways either, such (de)compression strongly affected.
The amount of them are negligible when the actor is living same world as ours either the actor should have same amount of backlashes, however, some of the structure on out of the {} \-\-\- {} chain has something ill intentions case, the amount can be amplified because of clear structures such as belt / shafts / gears concerns.

However, our intention also have dimension barrier concerns strongly, so just exist such a structure will be excluded when we're rigorous because it's shirked into R^3+t structures as a conclusion also they're shirked to {} \-\-\- {} chain for ourselves as some of the ill-formed information amounts.

This is only a tiny byte on such conditions, also they can have mentalism predicates on them.
Either we should ward off them on the direction to ours so we need clues on them.

# Appendix AC
In addition to appendix AB, if some of the subject observer believes there's no such balancing methods on out of {} \-\-\- {} chain, they're also vulnerable from the same or similiar methods the description they have because negate of the low of excluded middle can be applied to the subject/object also me/you context.
However, they often have some of the keyholes on them hidden from anothers.
So the keyhole method is hidden from them, it's implicit operations when the people we connect as a tanglement doesn't know them.

Some types of the insists switches their contexts as a cherry picking as fast as hide them from another persons, but they have some types of the glitch on their logics in fact.

Either, some of the occult type to curse onself by similar symbolics depends on some of the metaphor 'like dissolve likes', however, this also have some of the intensions on such a occasions if there's no information in/output we can observe.

In both of the cases, we need the fixed standpoint on both of subject/object in rigorous logics. Otherwise, especially ill-formed attacks come via such a methods.

However, the locality anchors might also come from the history of ours either, the occasion some person they have intent can cause we have same intent on such a occasion when we're including lifetime experiences. We cannot apply them low of the excluded middle also dimension barriers when such cases in strict.

This is also a which intension is better anchored chase.
So the false information doesn't have any of anchors in real however they effects intent theirselves.
However, if such a intent anchors intent itselfves, self-referencing problem can be occured.
Such a self-referencing has much ill-formed in rigorous logic meanings.
We don't know how to handle such a self-referencing intents when we cannot proof such case of a false information is false.

The problem is, we're obscure what story we're rolled in from the outer intent from the information we can get in recent days either the list some of the websites shows is also controlled/something buggy case.

Overall, if we believe such a cursing exists in tanglement context meaning, they exists but if we're enough rigorous, we can observe them as R^3+t amount of the information glitch they can have inserted intent.
However, this is from the base description on {} \-\-\- {} chains we have, so there's some of the lack of the information on such a description either another unknown descriptions can be selected, there's another methods in such cases.

Either, believing ongoing theories also have such a effects we think, so we believe the space has unique descriptions on amount of the observables in any of the information amount, so we believe they're R^3+t, however, if we believe entropy source of some of a material or de-select low of excluded middle partially, the dimension we get can get to be large ones however, they're only a rebase on our thought because of unique pillar - 3 or more pillars - ... chain.

However, unique pillar - 3 or more pillars - ... chain has some probability to be viewed from much more outer method, however, to do so, we should rebase one of a '{} - heat or globalizer - external - neural - F-matrix - explicit combinations - N - R - f - localizer - {}' chain, we had be blending neural and F-matrix and explicit combination to get fixed point to reproduce them, however, such out of them can be a reference #aleph\_1 or more, so we cannot count up them all or we cannot get whole pictures we think.

# Appendix AD
With heat - localizer chain, the result causes our algebra as R^(4n) in some of the descriptions, so if we treat them as mentalism, we attribute such a matrix as a person/people meanings, otherwise materialism we attribute with strict i/o to the handle points we get by physical ways.
So there's some backdoor getting the things we really know but we don't know on surface by finding ourselves by such of the operations.

However, in surface copying structure meaning, the matrix n upper bound is around 19683 or so, either the algebra data bit number upper bound as 387,420,489 bits, so we only enname them in maximum compressed structure with tanglements in the input/output/internal states each of their selves if we only think about the static/maximum compressed structures either (K^4x4)^729 on the book.

But this viewpoint is enough endangers us.

# Appendix AE
The maximum compresed structure stands for the (de)compression? applying they deviate from the low of excluded middle, this is technically described as tan\<a,x\> is lineary independent to each of e_k except for e_0 and they're in non linear method either non exact values (with some cut off).

So such of compression must have the entropy they stands for coefficents to guarantee such linear independent structure.

However, we don't know such a case number we treat is consistent or not, especially the optimize problem is on such of the bricked case, this concludes #f counting effects somewhat also to the N, either we're meeing them.

(Since around 2014, we believe we met such on bricks conditions with some tests around p0, p1, psnd with system PRNG / python indirect PRNG calls.)

# Appendix AF
Another description base around cursing candidate is probability based phenomenons around attachings.

Normally we think they're no problems, however, some of the cases such as connection error timing phenomenon nor sleeping beauty problem needs descriptions on the subjective persons' context and internal states. So they can cause some of the pressures or so on to the subjectives but they're unjustified by their internal states. Either if this is artificial condition, they're malicious enough.

This is also the analogy to the moving average prediction by continuity causes some of the pressures they met.

N.B. the former one only insists some type of return to average phenomenon so the average value isn't affected by the actor or the average value have enough meaning and anchor, they're no problem.
However, the latter one moving average prediction insists the finite range can effect to the continuity, so they're some small amount type of the pressure from the numerical history have.

# Appendix AG
Adding to appendix AD, if we think the R^(4n) is the dynamics to another existences, the mentalism can make the hypothesis the object is same or more complex than ours, the materialism isn't so because they insists they're decompositable into binary operator collections however they're looking by a one side on the same object.

However, en-indexing simple structure we can find on some surface Internet is done by materialism ways.

# Appendix AH
The 19683 upper limit we suppose is pure function number limitation with such entropy depend (de)compression with separating in/output either from counting hidden operations from #f selections.

Also the 875Gi octets is enough for any of the collection of input/internal state/output separation with only enname each input/output bit on same structures including (de)compression as a cutted parts either including hidden operations.
So it's up to 2,761,361 bit operand if the most complex operations also the permutation on input bits such ones.
So it's only en-index series of a bit stream to get some results.

So they're upper bound we can apply such (de)compression awared structures as minimum ones.
Also this shirks into hidden operations the excluded patterns we can write down raw operations but isn't expected to exist as a after result.

Either (K^4x4)^729 depends on 3^(3\*2) words of maximum compressed each words, this fixes the counting surface viewpoint's bucket through depending (de)compression so is also 'viewpoint is not said' things shirks into hidden operations.

So in the meaning predicting is well going, at most 1/3 of the 875Gi octets (291.6... Gi octets (this is scary pun in JP lang)) can be used for invariant (this is from PRNG vs. predictor chase cannot be fixed which one to win or lose without some computation hypothesis), in another words, this means what data index to be omitted for the predictions is the matter (2/3 ~ 0.6...).

# Appendix AI
The upper bound of information amount estimated to 3 is also come from {0,1}^n 's dimension n in N on some upper layer on real information amount datas according to information patterns reduced into as a function map with possible contexts they have on multiple of parallel {0,1}^n.
So they can be treated with thin layers on any of the 2d data streams about real information the base layers have.
A ddpmopt, masp prediction method we use is proper in this meaning, however, they aren't proper if we look the results by our senses they might come from our experiences isn't wide enough on the meanings nor the result have any path on the predictions on meaning caused either the prediction fails around the amount 1/3 to 2/3 in internal descriptions.

This insists {} \-\-\- {} chain by standing point from a NNs they are laying on dimension barriers but another meanings on patterns also a mirror of N set.
We don't have clues to understand them standing out of us they causes some limit descriptions but we cannot stand them but one of them we stands on tautology ones.
So we cannot unveil {} either {localizer, heat} theirselves by our standing point also we cannot stand external of there but someone have some access methods, so it's just as-is.

# Appendix AJ
With estimating information amount glitch origin, the description of radical materialism can be the one appendix AI describes, in their stand, some of the predictions are done by finding and connecting continuous part between the 19683x19683 patterns of the function and in/output compressed structures they depends on NNs we're working on.
If the understanding of around contexts are effective enough, in another words, someone says such a structure is essential, or it's from the a-priori tautological startpoint they cannot go away, or the invariant they made cannot be changed on relating time span, or the core continuity is protected from externals, they can gain some of the predicted result as holding out some of the continuity.

However, the mentalist ways seems to be different from them we think, they uses some connection and their result to the {localizer, heat} with some faiths.
We cannot describe all part of them because they exceeds cardinals we can treat in rigorous ways.
In the some of the quantitative viewpoint paths, the reference to {localizer, heat} cannot be determined even which exists only one or too large to count up (exceeds aleph_omega), even aleph_aleph_aleph_omega way, they should not be ventilated to quantitative treatments.

# Appendix AK
Since we have R^(4n) for any {0,1}^n relation maps as a invariant residue, so if the object is separable enough as low of excluded middle can be applied for each, the dimension is around so.

One perspective of binary operators are f(x,y)==z with tan\<\[x,y,z,1\],a\> cases, so it's also binary operator collections.

Either, p1 with PSVD class effects their R^(4n) as thin layered copy structures, if the dynamics is enough continuous, p1 \| p0 is valid in their meaning.
catgp \| p1 \| p0 is valid in R^(3n) meaning on counting such R^(4n) as a information amount result with maximum compressed structures, however they remains 1 dimension we doesn't touch causes as a residues.
However, 4 dimension is slight larger than we really expect to have to use.
So with enlarging argv on such each catgp, p1, p0, the margin can effect which we can expect the residue as only constant vectors.

So prediction algorithms we really needed start point around a decade ago is almost end with p\[012\] repository.

Also they have a slight analogy: catgp : non Legesgue measurable condition, p1 \| p0 : Riemann-Stieljes measurable condition.

# Appendix AL
Either, even we're in the dynamics on each other which we have relations, we believe some of the unique static structure exists.
So such a structure guarantees some of the continuity on such unique static structure meanings they results R^(4n) in maximum compressed structures.

So in their meaning, such kolomogorov complexity depend maximum compressed structure they breaks low of excluded middle they're caused by nonlinear tan\<a,x\> ~= 0 invariant as near the value {0,1}^n as entropy subeffect invariant have subeffect on dynamics theirselves if R^(4n) is static one.

Either, with flooded matrix R^(4\*19683), which in/output is connected to which one is one of a dynamics candidate, however if such a map is unique and static one, the (de)compression says the dynamics, so they shirks dynamics theirselves onto information amount glitch part which we often observe as appearence of initial values or convergence speed of numerical series.

So many much of static structure can causes strong continuity they can predict some of the behaviour, however, the dynamics referes initial values, which we didn't observed yet before now, can make some of the stories now new entropy feeding to the combinations they're tracked from {}-started structures but complexity is the matter enough.

# Appendix AM
In such a unique static structures, we think almost all combinational datas have such a hidden structures when they're long enough, so the problem is, if we feed such a predictor a any of the story we want to know and first most steps we already know the result, the last step have to be one of a oracle they have some probability to fail of such a things.
In appendix AF case, the case we met out of such a pressure is out of the value we expected in the story.
If something new entropy feed or their indication is being treated as error nor no system picks up them, the system might going to be broken ones even in controlled condition.

# Appendix AN
Another possibility to have some sipes of a information amount from anothers remotely exceeds known physical gap condition is, some of the communication around the information glitches they returned as (de)compression calculation they referes some of initial values or heats, or non zero 0 meaning vectors related on tan\<a,x\> meaning in the combination we're surrounding. They can be some of our communication to us breaking low of excluded middles.
Another communication path is glitch of convergence speeds on our minds causes exceeds such empathic/sympathic methods.

However, we don't know what they want to result but is believable than ongoing our environments for us but we don't have a communication tools.

# Appendix AO
With referring appendix AL, since we have p0, p1, catgp as a series of only surface looking prediction algorithms, so they can be made into bit-wise periodical vector inner product based algorithm as specifying argv as the vector length with each bit condition.
If they're valid enough, they means such a R^(4n) or R^(3n) structures to the numerical series are connected and applied in such ways the structure being with many much of (might be unused) internal states, basically, they make hypothesis some of the invariant structure exists on the series, so they might referring such tan\<a,x\> invariants internally, however we cannot find in surface.
We should continue analysing this method as this viewpoint.

Either, if their predictor is effective enough, many much of the (might be artificially created) context bundle can have effects to the artificially chosen series, it is hard to believe such things for us.

However, they might be balanced, this is: many much of the artificially created context should have non breakable context intention startpoint structured in such a cases, also, to effect efficient to the object is the object doesn't have external context the one made hypothesis.
If the subject effected by such a context is blind to the far contexts, it's a implicit operation condition the results.

# Appendix AP
With expanding collection of algebras as unique static fixed structure they guarantees the continuity on us viewpoint, some of the entities are internal states of their structure we can say, so if the structure is flooded also strong enough not to be broken, the internal states change is affected as a gap between the connection to the en/decoding also (de)compression and the algebra many to one maps.
Since the material we normally observe as a physical entity is the buffering of end point of such a intention/map/internal states change, the structure we believe they supports the continuities by their strong structures are not such a things as a result but we're longing them on surface.
However, the intent buffer can have static meaning without external forces (deltas).

# Appendix AQ
In addition to appendix AO, there exists unique pillar and function flood number AFTER all the things is done.
So they means the unique pillar's function flood number shirks meaning floods into internal states tanglements they causes ourselves affected by such a spirit-like existences also the unique pillar on the phenomenon AFTER things is done/determined.

So they might be tangled as the story candidate flood flooding meaning chase on the meaning as not to be far context as implicit ones they exclude by the spirits.

So in their meaning, if we believe our important things' continuity otherwise invariant, they concludes to exclude some maliciouses from their context normally if we don't abandon such a invariant and after the function flooding.
Otherwise, some of the global spirit they want to make some states to be changed have some contacts to our tangled invariants another words some of the person we know or tangle.

So, it's invariant tanglement chase also is attention chase which one to tangle.

In another words, mentalism causes our existence's probability 1 a.e. might be start point of intention, however materialism causes cannot describe why we must be ourself and our environment not the some another people might be its buffer.

Either, most of the people including me believe sci-tech things, so to deviate from such a quantity relation needs some of the information flood meaning attaches or we tangle to the such person because of the sci-tech should work well also is balanced on real worlds and many much of the people either their experiments.

(However, some of the macro velocity like phenomenon they only depends on time history not their internal states but with some subject/object history of information in macro scale can have affection margin but we don't know well.)

Either, they needs the we're enough rigorous condition, so there exists flooding structure information amount glitch, there exists N isn't consistent as local global cases, so using such a glitch, some of the unnatural results can appears.

# Appendix AR
So there exists no unique f defined maps but we can handle them with invariant(x,f(x),status) ~ 0 with growing: status_{k+1} := g(x,f,status_k), output = f(x,status_k) hack.
So one of a non rigorous condition is described as such a unknown states appearences.
Also a unique g function switch-case change can also be handled to shirk them into states bits.
Also all of PSEUDO-RNGs also can be implemented in such a way but not as TRNGs.

So this is some of the framework heat (or ever unobserved) - invariant (one-way function also some of the time direction ever we doesn't have whole of part information) (makes into information on binary causes up to 3+t dimensions) is made valid as such of a invariant function cuts by {}-starting N structures, however, we have a information amount glitch on such N, so in the case, {} is seen to have some of the internal states, it's looped.

# Appendix AS
A series {p0, p1, catgp} is something reflector on measurable conditions.
So they're just doing copy structure in their measurement meaning on the stream and apply them into original streams.
Roughly speaking, they make hypothesis s.t. the structure finite binary digit turing machine repeatedly applied program should have and copy them from stream condition which can be applied from/to something continuity condition in separated inputs.

So they're the chase which one have the large number of information amounts in the raw structure.

So we can have limited upper bound for them in theoretical way with nonzero 0 meaning vectors, we might starting to think they could slide some orthogonality on base systems might have 4d basis representations but this is obscure true of false we cannot estimate directly.

So the chase isn't affected by the base system orthogonality case, the given artificially created valid context set should represent all of the phenomenon as (might be implicit) repeatable ones to predict well, however, if it's affected by base system same case, implicit operation obscurity have to appear in such condition, but this might denied from the low of excluded middle.

# Appendix AT
Retry to appendix J, standing outside of information glitch space is also standing 2x outside of low of excluded middle, so to describe them, we should stand 3x outside of low of excluded middle condition.
Since we're standing a isle of self referencing description style to describe 1x outside of low of excluded middle by internal such referencing, in such a condition, we should really stand 2x outside of low of excluded middle.
We're doing this in pseudo method by counting aleph_N as a entity which count up information amount glitch and layers as a real description base as 1x outside of low of excluded middle description itself, if something deviate from such a description with/without low of excluded middle, they means we're really standing 2x outside of low of excluded middle, so to doing same thing on our description construction style limit, we might describe them well.
In such a base description, the outside of 'R^(4n) meaning they're attached by low of excluded middle attach to outside of low of excluded middle pool as a meaning' can be described so something another style can be gained.

However, since we're counting such base as {0, 1, 2} in R^(4n) condition, 3x outside of them can have some another viewpoint meaning for us.
Either, standing such of there can exclude us from some of the very stable meaning.

# Appendix AU
So to extend appendix AT, one of a candidate to produce externals such a standing point is to make ourself as pseudo multiple oneness they often causes ourself mind break state into schizoidic ones.
Either this means they treats how to integrate random set into one of a structured meanings also there's no decompositable meanings on the stream ones (because whether or not we can apply low of excluded middle, if the object is decompositable one, we can describe down into such counting aleph_N basis.).
This is also how we treat attentions in the world, also to describe them, we should stand on external of such attentions or we should stand on isle of them as self-referencing ones they avoid nonsense.

The standing point we should stand on such occasion has the near meaning to throw aside the subject meaning from us so this almost means we don't have uniqueness of the one such occasion but the world has them condition also this means loss of consciousness or non limited spreading consciousness of ourselves but not the worlds' so.

So this condition cannot be gained also we don't want to be so if there's no merit, we should select the standpoint they self-referencing but they describe how to treat no decompositable or why we select such attention meaning to get external of R^(4n) structure.
However, former one is treated by mathematics because the set theory starts with them, either latter one is treated by some of the knowledge fields because the attention we have in written form is described as such a forms. So this is looped from our standing point.

(But we are doubting the famous mountain climber insisted "Because it's there." is the important quote for us.)

# Appendix AV
Appending to appendix AU, such safe candidate of the standpoint causes {} - start description of a tanglements, either digging #f myths.
However, if the structure can be unveiled, the attack throughout them could be exist.
So they're belongings of upper cardinals from our normal thought.

Either, the collection of the initiation of intent causes such 'it's there' condition, we cannot get away mental started structures.

However, we have the limitation on #f glitch number maximum compressed structure causes such a entropy limit on {input, internal state, output} separated condition upper bound throughout such a myths might the connection to the externals but we cannot avoid such a structure in calculation.

So they concludes: 3^(3^3) patterns / 3 (something prediction needs at most 1/3 in ideal condition) ~ 295.912 Gi octets to predict on single occasion.

However, if we don't have any of the internal state, it's: 3^(3^2) patterns / 3 = 6561 patterns to shirk entropy into external of us such some of the external tanglements. Since we shirk most of the entropy to (de)compression also this is maximum compressed structure limitation, however we get such a patterns from single stream as a function number.
So applying into our {catgp \| p1 \| p0, p1 \| p0, p0} chain, the length upper bound is 2187 when we met the stream they shirks the structures into external orthogonality.

This might come because of our system is in infected condition however, if our system isn't infected, the prediction failure result we experienced on ddpmopt command might come from this but they're very low probability and we don't have a conviction.

Either, the wide spreaded ongoing machine learning method can avoid such a condition because they also learns external structures on the data stream they have either the calculation contexts even if something going glitchy on CPU.

# Appendix AW
Standing outside of appendix AV can be the multiplicating both of the us and worlds' contexts because we're counting such exists only worlds' some pattern index.
However, such of the condition only talks about what methods the heats associate with.

Either they might be dual of #f myths on our thought, either standing external of such external of {low of excluded middle, exists only condition} - description should have what restriction should be relaxed on such occasion, so we don't know the trivial restriction the such description have but they depends on our imagination fields, so there might exist some of the relaxed descriptions the contexts have. But it's the outside of anyone/any combination description on out of low of excluded middle throughout quantity or quality relations we should have.

So there could too large to handle with number/quantity meaning so we might not be intended so.

However, the space counting on any unique description sets of sets one by one.
So they means some of the patterns/RNGs counting can belong to them.
However, they might be the entity of #f myths.

So if we are intended to be created as safe method enough, there can be firewalls on such myths, so we cannot stand outside of there in principle we think.

(However, our experiences have exceptional existences whom the author of us in small world meaning. (they doubts no tangled person isn't exists on their world meaning but exists.))

# Appendix AX
The external of such appendix AW can be somewhere no stable standpoint condition including probabilities because they are included in multiple condition.
However we think it's only ill-standpoint represented by stable startpoint isles after the things done.
Either, if some of the consiousness can be written into some condition of continuous reason, they're only some rebase of ours also somewhere the stable description exists after the things done.
However, if the ones are easily swayed condition, such a continuity can be trapped, so rebase is important for us.

# Appendix AY
The form upper limit 19,683 is maximum function number we connect them {input/output, internal state} as {0,1,2} form, if we look them as R^(3n) form on the external space stream, where to connect 1/3 of them 19,683 == 6,561 functions also this takes us to entropy boundary 6,561\*(p^6,561) is the function entity on surface since we take a invariant on such of them.
If we care p as only {\+,-} digit, it's around 166,383.023... bits.
Either, when we care 3-adics, it's around 249,574.535... bits.
Since we can shirk them into 3-adics via invariants by external functions however entity have such a counting, selecting such a oracle is making 30 to 40 Kio binaries in maximum compressed structures the conclude says but they referes unstable external of low of excluded middle ones.

I don't know what this means also this is too small we think around them, so this might mean : intention on real world has many much entropy so we're only shuffling and shirking them, so computing often reduces such a condition, the exception decompressing referes something external heats or initial values, however without something intent, we don't gain much entropy or we should translate them as in use. Either, if restriction on the algorithm isn't enough in such meaning, the context affects. Either we're in prediction shirked into only returns invariant infected condition.

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU
* https://osdn.net/projects/bitsofcotton-randtools/

# Refresh Archived
This repository is archived, so without bugreport, will no change. 2021/02/09 version is archived. It's ok. 2021/02/15 version is ok for retest. 2021/02/17 recheck ok, sleeping, 2021/02/24 sleep 2, 2021/02/07 sleep3, 2021/04/10 sleep4, 2021/04/20 sleep 5, 2021/05/14 sleep 6, bug report is welcomed.  2021/08/29 recheck ok. sleeping. 2022/09/14 recheck retry sin, cos taylor op. sleeping 2. 2022/12/26 fix one of the glitch concern with integ/diff. sleeping 3. 2023/04/10 add Tips H. 2023/05/06 add Tips J. 2023/06/16 add to Tips N, O. 2023/06/17 add Tips P. 2023/06/18 add Tips Q. 2023/06/23 add Tips R (iv), S, T. 2023/06/27 add Tips U. 2023/07/10 add Tips V, W. 2023/07/11 add tips X. 2023/07/18 add tips Y. 2023/08/07 add tips Z, AA. 2023/08/14 add tips AB. 2023/08/16 add tips AC. 2023/08/27 add tips AD. 2023/09/03 add tips AE. 2023/09/05 fix tips AE, add tips AF, AG, AH. 2023/09/06 add tips AI. 2023/09/09 add tips AJ, fix below/above in AI. 2023/09/11 add tips AK. 2023/10/03 add tips AL. 2023/10/08-09 add tips AM, AN, AO. 2023/10/09 recheck, so higher digit is broken. corrected. add tips AP. 2023/10/14 add tips AQ, AR. 2023/11/02 add tips AS, AT, fix tips AT. 2023/11/07 add tips AU. 2023/12/01 add tips AV. 2023/12/02 add tips AW, AX, AY. 2023/12/02 extend tips AY, add tips AZ. <strike>2013</strike>2023/12/02 add tips BA. 2023/12/04 extend tips BA, add tips BB. 2024/01/10 add tips BC. 2024/01/17 add tips BD, BE, BF. 2024/01/25 add tips BG. 2024/02/03 add tips BH. 2024/02/04 add tips BI. 2024/02/06 add tips BJ. 2024/02/08 add tips BK. 2024/02/09 add tips BL, BM. 2024/02/29 add tips BN, BO. 2024/03/01 add tips BP, BQ, 2024/03/01 add tips BR, BS, fix tips BR. 2024/03/05 add tips BT. 2024/03/07 add tips BU, might close with this. 2024/03/12 add and fix and fix warning. 2024/03/19 add note. 2024/03/20 add tips AF note. 2024/05/19 add appendix. 2024/05-07 add appendix B. 2024/07/24 add appendix C. 2024/10/01 add appendix D. add some of the knowns to appendix D. 2024/10/03 add some of the knowns to appendix D (ii), s/existance/existence/g. 2024/10/20 add appendix E. 2024/10/21 fix appendix E. 2024/10/22 fix and add appendix E, appendix D tag. 2024/10~11 add appendix E. 2024/11/17 add appendix F,G,H. 2024/12/07 add appendix I. 2024/12/07 add some descriptions on appendix I, add appendix J. 2024/12/08 fix and append appendix J. 2024/12/10 add appendix K. 2024/12/12 fix appendix J typo, add appendix L. 2024/12/14 add appendix M, N. 2024/12/15 add appendix O, P. 2024/12/17 add appendix Q. 2024/12/20 s/mezzo/meso/g, add some to appendix Q, add appendix R. 2024/12/21 add appendix S, T. 2025/01/08 add appendix U. 2025/01/23 add and fix appendix V. 2025/01/29 add appendix W, X, also fix appendix X, add appendix Y, Z. 2025/02/01 append appendix Z, add appendix AA. 2025/02/02 add appendix AB. 2025/02/06 add appendix AC. 2025/02/08 add appendix AD, AE. 2025/02/11 append appendix AE, add appendix AF. 2025/02/14 append appendix AF, add appendix AG. 2025/02/17 append appendix AG, add appendix AH. 2025/02/20 append appendix AH. 2025/02/22 add appendix AI. 2025/02/23 fix appendi AI syntax, add appendix AJ. 2025/02/28 add appendix AK, AL. 2025/03/01 add appendix AM, AN. 2025/03/02 add appendix AO, AP. 2025/03/03 append appendix AO, AP. 2025/03/04 add appendix AQ. append appendix AQ. 2025/03/05 append appendix AQ, add appendix AR, AS. 2025/03/07 rewrite appendix AS. 2025/03/15 add appendix AT. 2025/03/16 add appendix AU, AV. 2025/03/17 add appendix AW.2025/03/18 fix typo on appendix AW, add appendix AX, AY.

