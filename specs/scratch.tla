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

Eval == IsUnique(<< 1, 1, 1, 1 >>)
ASSUME PrintT(Eval)
====
