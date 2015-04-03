from enum import Enum
from z3 import *
'''
  ==============
  The language of E
  ==============
  
  The language of E is six sorted, with sorts for
  (diagrammatic sorts) points, lines, circles,
  (metric assertions)  segments, angles, and areas.
  
  There are variables ranging over the first three sorts;
  
  a, b, c, ... to range over points
  L, M, N, ... to range over lines
  alpha, beta, gamma, ... to range over circles.
  
  There is =, <, 
  
  --------------
  Constants
  --------------
  right-angle of angle-sort, 0
    
  --------------
  Basic relations
  --------------
  on(a, L): point * line --> bool
  REQUIRES:
  ENSURES: true iff point a is on line L
  
  same-side(a,b,L): point * point * line --> bool
  REQUIRES: true
  ENSURES: true iff points a,b are on the same side of line L  
  
  between(a,b,c): point * point * point --> bool
  REQUIRES: a,b, and c are distinct and collinear
  ENSURES: true iff b is between a and c
  
  on(a,alpha): point * circle --> bool
  REQUIRES: true
  ENSURES: true iff point a is on circle alpha
  
  inside(a, alpha): point * circle --> bool
  REQUIRES: true
  ENSURES: point a is inside circle alpha
  
  center(a, alpha): point * circle --> bool
  REQUIRES: true
  ENSURES: true iff point a is in the center of circle alpha
  
  --------------
  Additional relations
  --------------
  
  intersects(L, M): line * line --> bool
  REQUIRES: true
  ENSURES: two lines intersect when they have exactly one point in common
  
  intersects(L, alpha): line * circle --> bool
  REQUIRES: true
  ENSURES: line and a circle intersect when they have exactly two points in common
  
  intersects(alpha, beta): circle * circle --> bool
  REQUIRES: true
  ENSURES: two circles intersect when they have exactly two points in common.

''' 

class PyEuclid (object):
    def __init__ (self):
        self.solver = Solver()
    
    """
      Declares all sorts, predicates, and functions. Adds
      the axioms of E to the solver.
    """
    def initLanguageCore (self):
        # # make sorts
        Point = DeclareSort("Point")
        Line = DeclareSort("Line")
        Circle = DeclareSort("Circle")        
        
        # # make basic relations between diagrammatic sorts
        Between = Function("Between", Point, Point, Point, BoolSort())
        OnLine = Function("On", Point, Line, BoolSort())
        OnCircle = Function("Onc", Point, Circle, BoolSort())
        Inside = Function ("Inside" , Point, Circle, BoolSort())
        Center = Function ("Center" , Point, Circle, BoolSort())
        SameSide = Function("SameSide", Point, Point, Line, BoolSort())
        Intersectsll = Function("Intersectsll", Line, Line, BoolSort())
        Intersectslc = Function("Intersectslc", Line, Circle, BoolSort())
        Intersectscc = Function("Intersectscc", Circle, Circle, BoolSort())
        
        # # make the magnitude sorts
        Segment = Function("Segment", Point, Point, RealSort())
        Angle = Function("Angle", Point, Point, Point, RealSort()) 
        Area = Function("Area", Point, Point, Point, RealSort())
        
        # # make constants/terms
        RightAngle = Const("RightAngle", RealSort())
        a, b, c, d, e = Consts('a b c d e', Point)
        L, M, N  = Consts('L M N' , Line)
        alpha, beta, gamma = Consts('alpha beta gamma', Circle)
        
        # # assert axioms for language E         
        axioms = [ ]
        
        """
            ---------- DIAGRAMMATIC AXIOMS ----------
        """
        """
          Two points determine a line
          1. If a != b, a is on L, and b is L, a is on M and b is on M,
          then L = M 
        """
        axioms.append( ForAll([a, b, L, M], \
            Implies(And(\
                Not(eq(a, b)), OnLine(a, L), OnLine(b, L),\
                OnLine(a, M), OnLine(b, M)),\
                     eq(L, M))))
        
        """
          Center of circle is unique
          2. if a and b are both centers of alpha then a=b
          3. if a is the center of alpha then a is inside alpha          
        """
        axioms.append( ForAll([a,b,alpha], \
            Implies( (And ( Center(a, alpha), Center(b, alpha))), eq(a,b))))
        axioms.append( ForAll([a,alpha], \
            Implies(Center(a,alpha), Inside(a, alpha))))
        
        """
          No degenerate circles
          4. if a is inside alpha, then a is not on alpha
        """
        axioms.append( ForAll([a,alpha] ,\
            Implies( Inside(a, alpha), Not(OnCircle(a, alpha)))))
        
        """
          Strict betweeness
          1. If b is between a and c then b is between c and a,
          a != b, a != c, and a is not between b and c
          2. If b is between a and c, a is on L, and b is on L, then c is on L.
          3. If b is between a and c, a is on L, and c is on L, then b is on L.
          4. If b is between a and c and d is between a and b then d is between a and c.
          5. If b is between a and c and c is between b and d then b is between a and d.
          6. if a, b, and c are distinct points on a line L, then either b is between a and c, or a is
          between b and c, or c is between a and b.
          
          7. if b is between a and c and b is between a and d then b is not between c and d.
        """
        
        axioms.append( ForAll([a,b,c],\
            Implies( Between(a,b,c),\
                And( Between(c,b,a), Not(eq(a,c)), Not(eq(a,b)), Not(Between(b,a,c)) ))))
        
        axioms.append( ForAll([a,b,c],\
            Implies( And(\
                Between(a,b,c), OnLine(a,L), OnLine(b,L)),\
                    OnLine(c,L))))
        
        axioms.append( ForAll([a,b,c],\
            Implies( And(\
                Between(a,b,c), OnLine(a,L), OnLine(c,L)),\
                    OnLine(b,L))))
        
        axioms.append( ForAll([a,b,c],\
            Implies( And(\
                Between(a,b,c), Between(a,d,b)),\
                    Between(a,d,c))))
        
        axioms.append( ForAll([a,b,c,d],\
            Implies( And(\
                Between(a,b,c), Between(b,c,d)), \
                    Between(a,b,d))))
        ## TODO: ask about "distinct points" on a line L
        axioms.append( ForAll([a,b,c, L],\
            Implies( And(\
                OnLine(a,L), OnLine(b,L), OnLine(c,L),\
                Not( eq(a, b)), Not(eq(a,c)), Not(eq(b,c))),\
                    Or( Between(a,b,c), Between(b,a,c), Between(a,c,b)))))
        
        axioms.append( ForAll([a,b,c,d],\
            Implies( And(\
                Between(a,b,c), Between(a,b,d)),\
                    Not(Between(d,b,c)))))
        
        
        """
          Same-side axioms
          1. if a is not on L, then a and a are on the same side of L.
          2. if a and b are on the same side of L, then b and a are on teh same side of L.
          3. if a and b are on the same side of L, then a is not on L.
          4. if a and b are on the same side of L, and a and c are on the same side of L, then b
           and c are on the same side L.
          5. if a,b, and c are not on L, and a and b are not on the same side of L,
           then either a
           and c are on the same side of L, or b 
        """
        
        axioms.append(ForAll([a,L],\
            Implies( Not( OnLine(a,L)),\
                SameSide(a,a,L))))
        axioms.append(ForAll([a,b,L],\
            Implies(SameSide(a,b,L), \
                And(Not(OnLine(a,L), SameSide(b,a,L))))))
        axioms.append(ForAll([a,b,c,L],\
            Implies( And(\
                SameSide(a,b,L), SameSide(a,c,L)),\
                    SameSide(b,c,L))))
        axioms.append(ForAll([ a,b,c,L],\
            Implies( And(\
                Not(OnLine(a,L)), Not(OnLine(b,L)), Not(OnLine(c,L))),\
                    Or(SameSide(a,b,L), SameSide(a,c,L), SameSide(b,c,L)))))
        
        ## TODO: check this axiom below with avigad, 
        ## "either a and c are sameside L, or b"
        ## is that sameside(a,c,L) or sameside(b,c,L) and NOT both?
        axioms.append(ForAll([a,b,c,L],\
            Implies(And(\
                Not(OnLine(a,L)), Not(OnLine(b,L)), Not(OnLine(c,L)),\
                Not(SameSide(a,b,L))),\
                    Or(SameSide(a,c,L), SameSide(b,c,L)))))
        
        """
           Pasch axioms
           1. if b is between a and c, and a and c are on the same side of L,
           then a and b are on teh same side of L.
           2. if b is between a and c, and a is on L and b is not on L,
           then b and c are on the same side of L.
           3. if b is between a and c and b is on L
           then a and c are not on the same side of L
           4. if b is the intersection of distinct lines L and M, a and c are distinct points on m,
           a != b, c !=b, and a and c are not on teh same side of L,
           then b is between a and c.       
        """
        axioms.append(ForAll([a,b,c,L],\
            Implies(And(\
                Between(a,b,c), SameSide(a,c,L)),\
                    SameSide(a,b,L))))
        
        axioms.append(ForAll([a,b,c,L],\
            Implies(And(\
                Between(a,b,c), OnLine(a,L), Not(OnLine(b,L))),\
                    SameSide(b,c,L))))
        
        axioms.append(ForAll([a,b,c,L],\
            Implies(And(\
                Between(a,b,c), OnLine(b,L)),\
                    Not(SameSide(a,c, L)))))
        
        axioms.append(ForAll([a,b,c,L,M],\
            Implies(And(\
                Not(eq(a, b)), Not(eq(b,c)), Not(eq(L,M)),\
                OnLine(a,M), OnLine(b,M), OnLine(c,M), Not(SameSide(a,c,L)), OnLine(b,L)),\
                    Between(a,b,c))))        
        """
           Triple incidence axioms
           1. if L, M, and N are lines meeting at a point a, and b, c, and d are points on L, M,and N resctively,
           and if c and d are on the same side of L, and b and c are on
           the same side of N, then b and d are not on the same side of M.
           2. if L,M,N are lines meeting at a point a, and b, c, and d are points on L M and N respectively, and 
           if c and d are on the same side of L, and b and d are not on the same side of M, and d is not on M 
           and b != a, 
           then b and c are on the same side of N.
           3. If L, M and N are lines meeting at a point a, and b, c, and d are points on L,M,
           and N respectively, and if c and d are on the same side of L, and b and c are on the
           same side of N, and d and e are on the sameside of M, and c and e are on the same side of N, 
           then c and e are on the same side of L.
        """
        axioms.append(ForAll([a, b, c, d, L, M, N],\
            Implies(And(\
                OnLine(a,L), OnLine(a,M), OnLine(a,N), OnLine(b,L), OnLine(c,M), OnLine(d,N),\
                SameSide(c,d,L), SameSide(b,c,N)),\
                    Not(SameSide(b,d,M)))))
        
        axioms.append(ForAll([a,b,c,d],\
            Implies(And(\
                OnLine(a,L), OnLine(a,M), OnLine(a,N),\
                OnLine(b,L), OnLine(c,M), OnLine(d,N),\
                SameSide(c,d,L), Not(SameSide(d,b,M)), Not(OnLine(d,M)), Not(eq(b,a))),\
                    SameSide(b,c,N))))
        
        axioms.append(ForAll([a,b,c,d,e,L,M,N],\
            Implies(And(\
                OnLine(a,L), OnLine(c,M), OnLine(a,N), OnLine(b,L),\
                OnLine(c,M), OnLine(d,N), SameSide(b,c,N), SameSide(d,c,L),\
                SameSide(d,e,M), SameSide(c,e,N)),\
                    SameSide(c,e,L))))
        """
            Circle axioms
        """
        
        axioms.append(ForAll([a,b,c,alpha,L],\
            Implies(And(\
                Inside(a,alpha), OnCircle(b,alpha), OnCircle(c,alpha),\
                OnLine(a,L), OnLine(b,L), OnLine(c,L), Not(eq(b,c))),\
                    Between(b,a,c))))
        
        axioms.append(ForAll([a,b,c,alpha],\
            Implies(And(\
                Or(Inside(a,alpha), OnCircle(a,alpha)), Or(Inside(b,alpha), OnCircle(b,alpha)),\
                Between(a,c,b)),\
                    And(Not(Inside(b,alpha)), Not(OnCircle(b,alpha))))))
        
        axioms.append(ForAll([a,b,c,alpha,L],\
            Implies(And(\
                Or(Inside(a,alpha), OnCircle(a,alpha)), Not(Inside(c,alpha)), Between(a,c,b)),\
                    And(Not(Inside(b,alpha)), Not(OnCircle(b,alpha))))))
        
        axioms.append(ForAll([a,b,c,d,alpha,beta],\
            Implies(And(\
                OnCircle(c,alpha), OnCircle(c,beta), OnCircle(d,alpha), OnCircle(d,beta),\
                Not(eq(alpha,beta)), Not(eq(c,beta)), OnLine(a,L), OnLine(b,L),\
                Center(a,alpha), Center(a,beta)),\
                    Not(SameSide(c,d,L)))))
        
        """
            Intersection
        """
        axioms.append(ForAll([L,M,a,b],\
            Implies(And(\
                OnLine(a,M), OnLine(b,M), Not(SameSide(a,b,L))),\
                    Intersectsll(L,M))))
        
        axioms.append(ForAll([alpha,L,a,b],\
            Implies(And(\
                Or(Inside(a,alpha), OnCircle(a,alpha)),\
                Or(Inside(b,alpha), OnCircle(b,alpha)),\
                Not(OnLine(a,L)), Not(OnLine(b,L)), Not(SameSide(a,b,L))),\
                    Intersectslc(L,alpha))))
        
        axioms.append(ForAll([L,alpha,a],\
            Implies(And(\
                Inside(a,alpha), OnLine(a,L)),\
                    Intersectslc(L,alpha))))
        
        ## TODO: check this one vvv
        axioms.append(ForAll([alpha,beta,a,b],\
            Implies(And(\
                OnCircle(a,alpha), Or(Inside(b,alpha), OnCircle(b,alpha)),\
                Inside(a,beta), Not(Inside(b,beta)), Not(OnCircle(b,beta))),\
                    Intersectscc(alpha,beta))))
        
        axioms.append(ForAll([alpha,beta,a,b],\
            Implies(And(\
                OnCircle(a,alpha), Inside(b,beta), Inside(a,beta), OnCircle(b,beta)),\
                    Intersectscc(alpha,beta))))
        
        """
            ---------- METRIC AXIOMS ----------
        """
        """
            Segments
        """
        axioms.append(ForAll([a,b],\
            Implies(eq(Segment(a,b), RealVal(0.0)), eq(a,b))))
        
        ## TODO: check >= and == do what their supposed to in this context
        axioms.append(ForAll([a],\
            Segment(a,a) == RealVal(0.0)))
        
        axioms.append(ForAll([a,b],\
            Segment(a,b) >= RealVal(0.0)))
        
        axioms.append(ForAll([a,b],\
            Segment(a,b) == Segment(b,a)))
        
        """
            Angles
        """
        
        
        
        
        ## TODO: [*] do Axioms 
        self.solver.add(axioms)
        res = lambda x: 'yes' if x=='sat' else 'no' 
        print ("Axiom Set Consistent? " + res(str(self.solver.check())))
        ## TODO: [*] how can we verify all these axioms.
        
def main():
    euclid = PyEuclid()
    euclid.initLanguageCore()
    
main()          
