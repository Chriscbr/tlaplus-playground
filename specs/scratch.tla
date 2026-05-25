---- MODULE scratch ----
EXTENDS Integers, TLC, Sequences, FiniteSets

MinutesToSeconds(m) == m * 60

\* representing time as <<hour, minute, second>>
ToSeconds(time) == time[1] * 3600 + time[2] * 60 + time[3]
Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)

ClockType == ( 0 .. 23 ) \X ( 0 .. 59 ) \X ( 0 .. 59 )
ClockTypeCardinality == Cardinality(ClockType)

\* Map
Squares == {x * x: x \in 1 .. 4}

\* Filter
Evens == {x \in 1 .. 4: x % 2 = 0}

\* Range
Range(seq) == {seq[i]: i \in 1 .. Len(seq)}

ToClock(seconds) ==
  LET seconds_per_day == 86400
  IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day

ToClock2(seconds) == LET h == seconds \div 3600
                         h_left == seconds % 3600
                         m == h_left \div 60
                         m_left == h_left % 60
                         s == m_left IN << h, m, s >>

IsComposite(num) == \E m, n \in 2 .. num: m * n = num

IsUnique(s) == Len(s) = Cardinality(Range(s))

st == [ a |-> 1, b |-> {} ]

\* Note: requires struct to have values of same type
RangeStruct(struct) == {struct[key]: key \in DOMAIN struct}

Zip(seq1, seq2) ==
  LET Min(a, b) == IF a < b THEN a ELSE b
      N == Min(Len(seq1), Len(seq2))
  IN [i \in 1 .. N |-> << seq1[i], seq2[i] >>
      ]
Zip2(seq1, seq2) ==
  LET N == ( DOMAIN seq1 ) \intersect ( DOMAIN seq2 )
  IN [i \in N |-> << seq1[i], seq2[i] >>
      ]

IsSorted(seq) == \A i, j \in 1 .. Len(seq): i < j => seq[i] <= seq[j]

\* Tells us the number of inputs in f that match val
CountMatching(f, val) == Cardinality({key \in DOMAIN f: f[key] = val})

Sort(seq) ==
  CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
    /\ \A i \in 1 .. Len(seq):
         CountMatching(seq, seq[i]) = CountMatching(sorted, seq[i])
    /\ IsSorted(sorted)

\* SeqMap(f, seq) == [i \in DOMAIN seq |-> f[seq[i]]]
SeqMap(Op(_), seq) == [i \in DOMAIN seq |-> Op(seq[i])]

Eval == Sort(<< 8, 2, 7, 4, 3, 1, 3 >>)
ASSUME PrintT(Eval)
====
