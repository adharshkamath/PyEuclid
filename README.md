# EuclidZ3
An automated Euclidean proof checker using SMT-solver Z3 (https://github.com/Z3Prover/z3)
and the Formal Language E (http://tinyurl.com/pbkqm59).
<\br>
To start working with Euclidean Proofs:
1) make sure z3 is in pythonpath
2) run python in EuclidZ3 folder
3) run "from core import * "
4) create a proof object "pc = Proof()"

Euclidean proofs have construction phases. There are three constructable
objects, Point, Line, Circle. See documentation for a list of their methods.
Constructable objects have pre- and post- conditions associated with them.
For example, constructing a line L through points a and b, has the pre-condition that a and b are distinct and the post-condition that a is on the line L and
b is on the line L.

Example:
  To create a line between two points: 
    a = Point("a")
    b = Point("b")
    L = Line("L")
    L.through(a,b)

Once a constructable object is declared, it can be passed to the Proof class.

Example:
  To construct L in proof (continuing from above examples:
    pc.construct(a)
    pc.construct(b)
    pc.construct(L)

Note that a and b are "constructed" in the Proof before L. Because L's preconditions require a and b, this must be so. Otherwise, Proof will complain that preconditions are not met.

In addition to constructions, it is possible to assert expressions to the proof
class using the hence method.
    


