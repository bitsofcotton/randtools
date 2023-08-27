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
There exists taylor series tan((op_{first digit}-.5)&pi;/6) == (det diag B x) \* (x_1 ...)^some m / (det diag B' x) / (x_1 ...)^some m on some cut off.
(<strike>rank sin, cos(op) == 2 because we make const. delta,</strike>pass all of the first large dimension multipliers into sin, cos taylors, then, do below, we can get the result. tan theta itself cannot be used because they doesn't converges).
With below, we get op\_{near bit} == \<y\*\*,\[1,x\]\>/\<y'\*\*,\[1,x\]\>.

# General Tips 7
punched.

# General Tips 8
So with below, A in Q^{n\*n} : random matrix, x in {0, 1}^n, Ax in first digit meaning seems to harden the PRNG
if original PRNG is better enough (long period and no bias on distribution.).

# General Tips 9
If we work with F\_p p in P, this description is also valid because x in F\_p, #((ax+b)|\_x:fix)==#(F\_p to F\_p) .
so zero condition is valid. (with lagrange multipliers, all condition is valid with op_{first digit} with general tips 4, 5 method with n to p\*n.).
So p-adic computer is also described with lagrange multipliers and same methods, by op_{first digit}, this is in Z.
We can also take op == \<y_0,x\>/\<y_1,x\>, x in {p, 1, ..., p - 1}^n with some extra small error.

p-adic is also checked by toeplitz(x) \* a == f(x) linear permutation, because a\*x+b\+... describes them.

and op':=op(x_1,...,x_n)-x_n+1=some f(x_1,...,x_n+1), we have invariant, in this case, we can get g as \<y, tan(\[1,x,s\])\> == 0 condition, s is status bits. Status bit is needed because of rank condition, but, s can be rewrited as some A\*\[1,x\].

N.B. we should choose \<y, arctan(\[1,x\])\> with this form, but arctan has not have periods in itself. To make periods valid, we choose tan(a\*y):=tan(Ax) to adjust them, so using invariant, each of variables are rewrited to be A\<y,tan(\[1,x,B x\])\>.

If we work with x := {x\_k in \[0, &alpha;\[} that float styled, the description \<y,tan(\[1,x,A\*x\])\> form is valid also in this method. So with this, \[- &alpha;, &alpha;\[ can be.

# General Tips A
If we deal with large enough matrix tan(\[1,x+,B\*x+\]):=A\*tan(\[1,x,B\*x\]),
with smaller A', tan(\[1,x(small)+,B'\*x(small)+\])=
A'\*tan(\[1,x(small),B'\*x(small)\]).
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
with A\[tan(x) tan(B\*x) tan(y) tan(C\*y)\]-&gt;0 matrix.
So if we can find an invariant on the data series with some expanded dimensions, we can define a mapping.

# General Tips D
punched.

# General Tips E
Only for invariant meaning, we can bet 0==arcsin(sin(\<a, x\>)) on the form, so it's also the form 0==\<a, x\>\*(x_1...x_n)^m (exists m for some error).
So linear invariant meaning from the data, it's also the form: \<d_k, x\>\/(x_1...x_n)^m is ok. So d_k into variable, it's \<d_k, x\>\/(d_1...d_n)^m.
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

# Another Download Sites
* https://drive.google.com/drive/folders/1B71X1BMttL6yyi76REeOTNRrpopO8EAR?usp=sharing
* https://1drv.ms/u/s!AnqkwcwMjB_PaDIfXya_M3-aLXw?e=qzfKcU
* https://osdn.net/projects/bitsofcotton-randtools/

# Refresh Archived
This repository is archived, so without bugreport, will no change. 2021/02/09 version is archived. It's ok. 2021/02/15 version is ok for retest. 2021/02/17 recheck ok, sleeping, 2021/02/24 sleep 2, 2021/02/07 sleep3, 2021/04/10 sleep4, 2021/04/20 sleep 5, 2021/05/14 sleep 6, bug report is welcomed.  2021/08/29 recheck ok. sleeping. 2022/09/14 recheck retry sin, cos taylor op. sleeping 2. 2022/12/26 fix one of the glitch concern with integ/diff. sleeping 3. 2023/04/10 add Tips H. 2023/05/06 add Tips J. 2023/06/16 add to Tips N, O. 2023/06/17 add Tips P. 2023/06/18 add Tips Q. 2023/06/23 add Tips R (iv), S, T. 2023/06/27 add Tips U. 2023/07/10 add Tips V, W. 2023/07/11 add tips X. 2023/07/18 add tips Y. 2023/08/07 add tips Z, AA. 2023/08/14 add tips AB. 2023/08/16 add tips AC. 2023/08/27 add tips AD.

