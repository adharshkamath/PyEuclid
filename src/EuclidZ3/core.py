from z3 import Solver, DeclareSort, Function, BoolSort, RealSort, Const, Consts, \
    ForAll, And, eq, Not, Implies, Or, RealVal, Context, Distinct, simplify, \
    ExprRef, is_const
import sets


class LanguageE(object):
    '''   
 @author: krojas
 
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
    
    def __init__(self):
        '''
        Constructor
        '''
        print "=== Initializing language EuclidZ3 ==="
        
        # # make sorts
        self.PointSort = DeclareSort("Point")
        self.LineSort = DeclareSort("Line")
        self.CircleSort = DeclareSort("Circle")        
        
        # # make basic relations between diagrammatic sorts
        self.Between = Function("Between", self.PointSort, self.PointSort, self.PointSort, BoolSort())
        self.OnLine = Function("On", self.PointSort, self.LineSort, BoolSort())
        self.OnCircle = Function("Onc", self.PointSort, self.CircleSort, BoolSort())
        self.Inside = Function ("Inside" , self.PointSort, self.CircleSort, BoolSort())
        self.Center = Function ("Center" , self.PointSort, self.CircleSort, BoolSort())
        self.SameSide = Function("SameSide", self.PointSort, self.PointSort, self.LineSort, BoolSort())
        self.Intersectsll = Function("Intersectsll", self.LineSort, self.LineSort, BoolSort())
        self.Intersectslc = Function("Intersectslc", self.LineSort, self.CircleSort, BoolSort())
        self.Intersectscc = Function("Intersectscc", self.CircleSort, self.CircleSort, BoolSort())
        
        # # make the magnitude sorts
        self.Segment = Function("Segment", self.PointSort, self.PointSort, RealSort())
        self.Angle = Function("Angle", self.PointSort, self.PointSort, self.PointSort, RealSort()) 
        self.Area = Function("Area", self.PointSort, self.PointSort, self.PointSort, RealSort())
        
        # # make constants/terms
        self.RightAngle = Const("RightAngle", RealSort())
        a, b, c, d, e = Consts('a b c d e', self.PointSort)
        L, M, N = Consts('L M N' , self.LineSort)
        alpha, beta = Consts('alpha beta', self.CircleSort)
        
        # # assert self.axioms for language E         
        self.axioms = [ ]
        
        """
            ---------- DIAGRAMMATIC AXIOMS ----------
        """
        """
          Two points determine a line
          1. If a != b, a is on L, and b is L, a is on M and b is on M,
          then L = M 
        """
        self.axioms.append(ForAll([a, b, L, M], \
            Implies(And(\
                Not(a == b), self.OnLine(a, L), self.OnLine(b, L), \
                self.OnLine(a, M), self.OnLine(b, M)), \
                     L == M)))
        
        """
          self.Center of circle is unique
          2. if a and b are both centers of alpha then a=b
          3. if a is the center of alpha then a is inside alpha          
        """
        self.axioms.append(ForAll([a, b, alpha], \
            Implies((And (self.Center(a, alpha), self.Center(b, alpha))), a == b)))
        self.axioms.append(ForAll([a, alpha], \
            Implies(self.Center(a, alpha), self.Inside(a, alpha))))
        
        """
          No degenerate circles
          4. if a is inside alpha, then a is not on alpha
        """
        self.axioms.append(ForAll([a, alpha] , \
            Implies(self.Inside(a, alpha), Not(self.OnCircle(a, alpha)))))
        
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
        
        self.axioms.append(ForAll([a, b, c], \
            Implies(self.Between(a, b, c), \
                And(self.Between(c, b, a), Not(a == c), Not(a == b), Not(self.Between(b, a, c))))))
        
        self.axioms.append(ForAll([a, b, c], \
            Implies(And(\
                self.Between(a, b, c), self.OnLine(a, L), self.OnLine(b, L)), \
                    self.OnLine(c, L))))
        
        self.axioms.append(ForAll([a, b, c], \
            Implies(And(\
                self.Between(a, b, c), self.OnLine(a, L), self.OnLine(c, L)), \
                    self.OnLine(b, L))))
        
        self.axioms.append(ForAll([a, b, c], \
            Implies(And(\
                self.Between(a, b, c), self.Between(a, d, b)), \
                    self.Between(a, d, c))))
        
        self.axioms.append(ForAll([a, b, c, d], \
            Implies(And(\
                self.Between(a, b, c), self.Between(b, c, d)), \
                    self.Between(a, b, d))))
        
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(b, L), self.OnLine(c, L), \
                Not(a == b), Not(a == c), Not(b == c)), \
                    Or(self.Between(a, b, c), self.Between(b, a, c), self.Between(a, c, b)))))
        
        self.axioms.append(ForAll([a, b, c, d], \
            Implies(And(\
                self.Between(a, b, c), self.Between(a, b, d)), \
                    Not(self.Between(d, b, c)))))
        
        
        """
          Same-side self.axioms
          1. if a is not on L, then a and a are on the same side of L.
          2. if a and b are on the same side of L, then b and a are on teh same side of L.
          3. if a and b are on the same side of L, then a is not on L.
          4. if a and b are on the same side of L, and a and c are on the same side of L, then b
           and c are on the same side L.
          5. if a,b, and c are not on L, and a and b are not on the same side of L,
           then either a
           and c are on the same side of L, or b 
        """
        
        self.axioms.append(ForAll([a, L], \
            Implies(Not(self.OnLine(a, L)), \
                self.SameSide(a, a, L))))
        self.axioms.append(ForAll([a, b, L], \
            Implies(self.SameSide(a, b, L), \
                And(Not(self.OnLine(a, L), self.SameSide(b, a, L))))))
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.SameSide(a, b, L), self.SameSide(a, c, L)), \
                    self.SameSide(b, c, L))))
        self.axioms.append(ForAll([ a, b, c, L], \
            Implies(And(\
                Not(self.OnLine(a, L)), Not(self.OnLine(b, L)), Not(self.OnLine(c, L))), \
                    Or(self.SameSide(a, b, L), self.SameSide(a, c, L), self.SameSide(b, c, L)))))
        
        # # TODO: check this axiom below with avigad, 
        # # "either a and c are sameside L, or b"
        # # is that sameside(a,c,L) or sameside(b,c,L) and NOT both?
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                Not(self.OnLine(a, L)), Not(self.OnLine(b, L)), Not(self.OnLine(c, L)), \
                Not(self.SameSide(a, b, L))), \
                    Or(self.SameSide(a, c, L), self.SameSide(b, c, L)))))
        
        """
           Pasch self.axioms
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
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.Between(a, b, c), self.SameSide(a, c, L)), \
                    self.SameSide(a, b, L))))
        
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.Between(a, b, c), self.OnLine(a, L), Not(self.OnLine(b, L))), \
                    self.SameSide(b, c, L))))
        
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.Between(a, b, c), self.OnLine(b, L)), \
                    Not(self.SameSide(a, c, L)))))
        
        self.axioms.append(ForAll([a, b, c, L, M], \
            Implies(And(\
                Not(a == b), Not(b == c), Not(L == M), \
                self.OnLine(a, M), self.OnLine(b, M), self.OnLine(c, M), Not(self.SameSide(a, c, L)), self.OnLine(b, L)), \
                    self.Between(a, b, c))))        
        """
           Triple incidence self.axioms
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
        self.axioms.append(ForAll([a, b, c, d, L, M, N], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(a, M), self.OnLine(a, N), self.OnLine(b, L), self.OnLine(c, M), self.OnLine(d, N), \
                self.SameSide(c, d, L), self.SameSide(b, c, N)), \
                    Not(self.SameSide(b, d, M)))))
        
        self.axioms.append(ForAll([a, b, c, d], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(a, M), self.OnLine(a, N), \
                self.OnLine(b, L), self.OnLine(c, M), self.OnLine(d, N), \
                self.SameSide(c, d, L), Not(self.SameSide(d, b, M)), Not(self.OnLine(d, M)), Not(b == a)), \
                    self.SameSide(b, c, N))))
        
        self.axioms.append(ForAll([a, b, c, d, e, L, M, N], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(c, M), self.OnLine(a, N), self.OnLine(b, L), \
                self.OnLine(c, M), self.OnLine(d, N), self.SameSide(b, c, N), self.SameSide(d, c, L), \
                self.SameSide(d, e, M), self.SameSide(c, e, N)), \
                    self.SameSide(c, e, L))))
        """
            Circle self.axioms
        """
        
        self.axioms.append(ForAll([a, b, c, alpha, L], \
            Implies(And(\
                self.Inside(a, alpha), self.OnCircle(b, alpha), self.OnCircle(c, alpha), \
                self.OnLine(a, L), self.OnLine(b, L), self.OnLine(c, L), Not(b == c)), \
                    self.Between(b, a, c))))
        
        self.axioms.append(ForAll([a, b, c, alpha], \
            Implies(And(\
                Or(self.Inside(a, alpha), self.OnCircle(a, alpha)), Or(self.Inside(b, alpha), self.OnCircle(b, alpha)), \
                self.Between(a, c, b)), \
                    And(Not(self.Inside(b, alpha)), Not(self.OnCircle(b, alpha))))))
        
        self.axioms.append(ForAll([a, b, c, alpha, L], \
            Implies(And(\
                Or(self.Inside(a, alpha), self.OnCircle(a, alpha)), Not(self.Inside(c, alpha)), self.Between(a, c, b)), \
                    And(Not(self.Inside(b, alpha)), Not(self.OnCircle(b, alpha))))))
        
        self.axioms.append(ForAll([a, b, c, d, alpha, beta], \
            Implies(And(\
                self.OnCircle(c, alpha), self.OnCircle(c, beta), self.OnCircle(d, alpha), self.OnCircle(d, beta), \
                Not(alpha == beta), Not(c == d), self.OnLine(a, L), self.OnLine(b, L), \
                self.Center(a, alpha), self.Center(a, beta)), \
                    Not(self.SameSide(c, d, L)))))
        
        """
            Intersection
        """
        self.axioms.append(ForAll([L, M, a, b], \
            Implies(And(\
                self.OnLine(a, M), self.OnLine(b, M), Not(self.SameSide(a, b, L))), \
                    self.Intersectsll(L, M))))
        
        self.axioms.append(ForAll([alpha, L, a, b], \
            Implies(And(\
                Or(self.Inside(a, alpha), self.OnCircle(a, alpha)), \
                Or(self.Inside(b, alpha), self.OnCircle(b, alpha)), \
                Not(self.OnLine(a, L)), Not(self.OnLine(b, L)), Not(self.SameSide(a, b, L))), \
                    self.Intersectslc(L, alpha))))
        
        self.axioms.append(ForAll([L, alpha, a], \
            Implies(And(\
                self.Inside(a, alpha), self.OnLine(a, L)), \
                    self.Intersectslc(L, alpha))))
        
        self.axioms.append(ForAll([alpha, beta, a, b], \
            Implies(And(\
                self.OnCircle(a, alpha), Or(self.Inside(b, alpha), self.OnCircle(b, alpha)), \
                self.Inside(a, beta), Not(self.Inside(b, beta)), Not(self.OnCircle(b, beta))), \
                    self.Intersectscc(alpha, beta))))
        
        self.axioms.append(ForAll([alpha, beta, a, b], \
            Implies(And(\
                self.OnCircle(a, alpha), self.Inside(b, beta), self.Inside(a, beta), self.OnCircle(b, beta)), \
                    self.Intersectscc(alpha, beta))))
        
        """
            ---------- METRIC AXIOMS ----------
        """
        """
            Segments
        """
        self.axioms.append(ForAll([a, b], \
            Implies(self.Segment(a, b) == RealVal(0.0), a == b)))
        
        self.axioms.append(ForAll([a], \
            self.Segment(a, a) == RealVal(0.0)))
        
        self.axioms.append(ForAll([a, b], \
            (self.Segment(a, b) >= RealVal(0.0))))
        
        self.axioms.append(ForAll([a, b], \
            self.Segment(a, b) == self.Segment(b, a)))
        
        """
            Angles
        """
        
        self.axioms.append(ForAll ([a, b, c], \
            Implies(And(\
                Not(a == b), Not(b == c)), \
                    self.Angle(a, b, c) == self.Angle(c, b, a))))
        
        self.axioms.append(ForAll ([a, b, c], \
            Implies(And(\
                Not((a == b)), Not((b == c))), \
                    And(\
                        self.Angle(a, b, c) >= RealVal(0.0), \
                        self.Angle(a, b, c) <= (self.RightAngle + self.RightAngle)))))
        
        """
            Areas
        """
        
        self.axioms.append(ForAll([a, b], \
            self.Area(a, a, b) == RealVal(0.0)))
        
        self.axioms.append(ForAll([a, b, c], \
            self.Area(a, b, c) >= RealVal(0.0)))
        
        self.axioms.append(ForAll([a, b, c], \
            And(self.Area(a, b, c) == self.Area(c, a, b), self.Area(a, b, c) == self.Area(b, a, c))))
        
        """
            ---------- Transfer AXIOMS ----------
        """
        
        """
            Diagram-segment transfer self.axioms
        """
        self.axioms.append(ForAll([a, b, c], \
            Implies(self.Between(a, b, c), ((self.Segment(a, b) + self.Segment(b, c)) == self.Segment(a, c)))))
        
        # # center and radius determine circle
        self.axioms.append(ForAll([a, b, c, alpha, beta], \
            Implies(And(\
                self.Center(a, alpha), self.Center(a, beta), self.OnCircle(b, alpha), self.OnCircle(c, beta), \
                self.Segment(a, b) == self.Segment(a, c)), \
                    (alpha == beta))))
        
        self.axioms.append(ForAll([a, b, c, alpha], \
            Implies(And(self.Center(a, alpha), self.OnCircle(b, beta), self.Segment(a, c) == self.Segment(a, b)), \
                self.OnCircle(c, alpha))))
        
        self.axioms.append(ForAll([a, b, c, alpha], \
            Implies(And(\
                self.Center(a, alpha), self.OnCircle(b, alpha)), \
                    ((self.Segment(a, c) == self.Segment(a, b)) == self.Inside(c, alpha)))))
        
        
        """
            Diagram-angle transfer self.axioms
        """
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                Not((a == b)), Not((a == c)), self.OnLine(a, L), self.OnLine(b, L)), \
                    (And(self.OnLine(c, L), Not(self.Between(c, a, b))) == (self.Angle(b, a, c) == RealVal(0.0))))))
        
        # # Possibly this is superfluous 
        self.axioms.append(ForAll([a, b], \
            Implies(Not((a == b)), self.Angle(a, b, a) == RealVal(0.0))))
        
        # # Point inside angle iff angles sum
        self.axioms.append(ForAll([a, b, c, d, L, M], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(b, L), self.OnLine(a, M), self.OnLine(c, M), \
                Not((a == b)), Not((a == c)), Not(self.OnLine(d, L)), Not(self.OnLine(d, M)), \
                Not((L == M))), \
                    ((self.Angle(b, a, c) == (self.Angle(b, a, d) + self.Angle(d, a, c))) == \
                        And(self.SameSide(b, d, M), self.SameSide(d, c, L))))))
        
        # # Define right angle (and all right angles are equal)
        self.axioms.append(ForAll([a, b, c, d, L], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(b, L), self.Between(a, c, b), Not(self.OnLine(d, L))), \
                    ((self.Angle(a, c, d) == self.Angle(d, c, b)) == (self.Angle(a, c, d) == self.RightAngle)))))
        
        """
            Diagram-area transfer self.axioms
        """
        self.axioms.append(ForAll([a, b, c, L], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(b, L), Not((a == b))), \
                    ((self.Area(a, b, c) == RealVal(0.0)) == self.OnLine(c, L)))))
        
        # # Sum of Areas
        self.axioms.append(ForAll([a, b, c, d, L], \
            Implies(And(\
                self.OnLine(a, L), self.OnLine(b, L), self.OnLine(c, L), Not(self.OnLine(d, L)), \
                Not((a == b)), Not((c == a)), Not((c == b))), \
                    (self.Between(a, c, b) == ((self.Area(a, c, d) + self.Area(d, c, b)) == self.Area(a, d, b))))))
         
         
        
        
        self.solver = Solver()
        self.solver.add(self.axioms)
        
        print "Axiom set : " + str(self.solver.check())

class Proof(object):
    '''
    Proof class provides an interface with z3 for
    checking Euclidean proofs in the language E.
    
    Its keeps tracks of objects created, assumptions, and conclusions.
    It can carry out construction of GeometricObjects
    '''

    def __init__(self):
        '''
        Constructor
        '''           
        print "=== Initializing proof checker ==="
        self.language = language
        self.solver = language.solver
        self.points = dict()
        self.lines = dict()
        self.circles = dict()
        ## TODO: make constructableobjects and expression hashable so they
        ## can be stored in a set instead of a list. Increase performance,
        ## remove annoying duplicates.
        self.assumptions = []
        self.conclusions = []  
    
    def point(self,point):
        '''
        returns the constructable object with specified label.
        '''
        result = self.points.get(point)
        if result == None:
            print "ProofCheck >> No such point constructed"
            return None
        return result   
    
    def hence(self, expr):
        '''
        Checks if expression follows from facts and axioms.
        if so, the expression is made explicit
        '''
        self.solver.push()
        self.solver.add(expr)
        result = self.solver.check()
        if str(result) != 'sat':
            print "ProofCheck >> Does not follow : " + str(expr)
            self.solver.pop()
            return False
        
        self.conclusions.append(expr)
        self.solver.pop()
        self.solver.add(expr)
        return True         
        
    def construct(self, obj):
        '''
        Takes in a ConstructableObject with preconditions
        and postconditions. Checks that preconditions hold
        in the proof context and if so, asserts the post-conditions.
        '''
        self.solver.push()
        for prereq in obj.prereqs:
            self.solver.add(simplify(prereq, blast_distinct = True))
            prereqCheck = self.solver.check()
            if str(prereqCheck) != 'sat':
                print "ProofCheck >> Construction Failed - Could not meet: " + str(prereq) 
                self.solver.pop()
                return False
            
        if len(obj.prereqs) > 0:
            self.assumptions.extend(obj.prereqs)
            
        for conclusion in obj.conclusions:
            self.solver.add(simplify(conclusion, blast_distinct=True))
            self.conclusions.append(conclusion)
        
        if isinstance(obj, Point):
            self.points[obj.label] = obj
        elif isinstance(obj, Line):
            self.lines[obj.label] = obj
        elif isinstance(obj, Circle):
            self.circles[obj.label] = obj
            
        self.solver.pop()
        self.solver.add(obj.prereqs)
        self.solver.add(obj.conclusions)
        return True
    
            
    
    def status(self):
        '''
        Returns a string representing this proof's status.
        '''
        ## TODO: should display theorems and goals
        return "~~~~~   \n" + \
        "pts: " + str(self.points.keys()) + "\n" + \
        "lines: " + str(self.lines.keys()) + "\n" + \
        "circles: " + str(self.circles.keys()) + "\n" + \
        "~\n" + \
        "assumptions: " + str(self.assumptions) + "\n" + \
        "conclusions: " + str(self.conclusions) + "\n~~~~~"
     
    def __str__(self, *args, **kwargs):
        return self.status()   
    

class Theorem(object):
    '''
        This is a theorem in the language E.
    '''
    ## TODO: overhaul this entire class. 
    ## it should work like a MultiplyLinkedList, one theorem is a justification
    ## for others. This is where non-linear deduction gets support
    def __init__(self):
        self.assumedObjects = []
        self.assumedProperties = []
        self.desiredObjects = []
        self.desiredConclusions = []
    
    
    def proclusTerm(self):
        if len(self.desiredObjects) == 0:
            return "Proclus Theorem"
        return "Proclus Problem"
    
    def __str__(self):
        return str(self.assumedObjects) + ", "\
             + str(self.assumedProperties) + \
             " ==> " + str(self.desiredObjects) + \
             ", " + str(self.desiredConclusions)
    
    
## TODO: create AbstractConstructableObject class to provide Template methods
## for Point, Line, Circle
class Point(object):
    
    '''
    This class represents a Point in a euclidean proof.
    It is a wrapper for the PointSort and the various
    functions operating on it, as defined in 
    LanguageE.
    
    Once all desired properties are applied to this Point
    you can call this Point's construct method. 
    '''
    
    def __init__(self, label, isDistinct=True):
        '''
        Point constructor. Label should be 1 or so characters with
        no spaces, e.g. 'p' . You can construct multiple points
        with the same constraints but different labels if the
        label has the for 'p q r' . 
        
        For example, Point('p q r') represents 3 distinct points
        '''
        self.label = label
        self.isDistinct = isDistinct  
        self.prereqs = []
        self.conclusions = []
        self.z3Expr = Const(label, language.PointSort)
        if self.isDistinct:
            self.conclusions.append(Distinct(self.z3Expr))
    
    def __eq__(self, other):
        '''
        returns the equality of the z3 expressions representing
        the objects being compared
        '''
        if not isinstance(other, Point):
            return False
        return self.z3Expr == other.z3Expr
    
    
    
    
    def __str__(self, *args, **kwargs):
        return "|Point [" + str(self.z3Expr) + "] :\n" +\
                "|   prereq: " + str(self.prereqs) + "\n" + \
                "|   concls: " + str(self.conclusions) + "\n"
    
    def onLine(self, line):
        '''
        specify construction should place point on line
        '''
        self.prereqs.append(Distinct(line.z3Expr))
        self.conclusions.append(language.OnLine(self.z3Expr, line.z3Expr))
        
    def onCircle(self, circle):
        '''
        Specify construction should place point on circle
        '''
        self.prereqs.append(Distinct(circle.z3Expr))
        self.conclusions.append(language.OnCircle(self.z3Expr, circle.z3Expr))
    
    def between(self, point1, point2):
        '''
        Specify construction should place this point between point1 and point2
        '''
        self.prereqs.append(Not(point1.z3Expr == point2.z3Expr))   
        self.conclusions.append(language.Between(point1.z3Expr, self.z3Expr, point2.z3Expr))
    
    def sameside(self, point, line):
        '''
        Specify this construction should place this point on sameside of line 
        as another point
        '''
        self.prereqs.append(Not(language.OnLine(point.z3Expr, line.z3Expr)))
        self.conclusions.append(language.SameSide(self.z3Expr, point.z3Expr, line.z3Expr))
        
    def opposite(self, point, line):
        '''
        Specify this construction should place this point opposite of line
        '''
        self.prereqs.append(Not(language.OnLine(point.z3Expr, line.z3Expr)))
        self.conclusions.append(Not(language.SameSide(self.z3Expr, point.z3Expr, line.z3Expr)))
        self.conclusions.append(Not(language.OnLine(self.z3Expr, line.z3Expr)))
        
    def inside(self, circle):      
        '''
        Specify this construction should plae this point inside circle
        '''  
        self.conclusions.append(language.Inside(self.z3Expr, circle.z3Expr))           
                  
    def outside(self, circle):
        '''
        Specify this construction should place this point outside circle
        '''
        self.conclusions.append(Not(language.Inside(self.z3Expr, circle.z3Expr)))
    
    def intersectsLines(self, line1, line2):
        '''
        Specify this construction should place this point on intersection of 
        lines
        '''
        ## TODO: make these functions take lists of objects too
        self.prereqs.append(language.Intersectsll(line1.z3Expr, line2.z3Expr))
        self.conclusions.append(language.OnLine(self.z3Expr, line1.z3Expr))
        self.conclusions.append(language.OnLine(self.z3Expr, line2.z3Expr))
    
    def intersectsCircleLine(self, circle, line):
        '''
        Specify this construction should place this point on intersection
        of circle and line
        '''
        self.prereqs.append(language.Intersectslc(line.z3Expr, circle.z3Expr))
        self.conclusions.append(language.OnCircle(self.z3Expr, circle.z3Expr))
        self.conclusions.append(language.OnLine(self.z3Expr, line.z3Expr))

    def intersectsCircleCircle(self, circle1, circle2):
        '''
        Specify this construction should place this point on intersection of
        circle and circle
        '''
        self.prereqs.append(language.Intersectscc(circle1.z3Expr, circle2.z3Expr))
        self.conclusions.append(language.OnCircle(self.z3Expr, circle1.z3Expr ))
        self.conclusions.append(language.OnCircle(self.z3Expr, circle2.z3Expr))
        


class Line(object):
    
    '''
    Line constructor. 
    '''
    def __init__(self, label, isDistinct=True):
        self.label = label
        self.isDistinct = isDistinct  
        self.prereqs = []
        self.conclusions = []
        self.z3Expr = Const(label, language.LineSort)
        if self.isDistinct:
            self.conclusions.append(Distinct(self.z3Expr))
    
    def __eq__(self, other):
        if not isinstance(other, Line):
            return False
        return self.z3Expr == other.z3Expr
       
    def __str__(self, *args, **kwargs):
        return "|Line [" + str(self.z3Expr) + "] :\n" +\
                "|   prereq: " + str(self.prereqs) + "\n" + \
                "|   concls: " + str(self.conclusions) + "\n"

    
    def through(self, point1, point2):
        '''
        Specify that this construction should place line through
        points 1 and 2
        '''
        ## TODO: there is a problem with equality statements like this
        ## z3 complains that: "warning: an assumption must be a propositional
        ## variable or the negation of one. I've tried equality == and 'is'
        self.prereqs.append(Not(point1.z3Expr == point2.z3Expr))
        self.conclusions.append(language.OnLine(point1.z3Expr, self.z3Expr))
        self.conclusions.append(language.OnLine(point2.z3Expr, self.z3Expr))
    
    

class Circle(object):
    
    '''
    Circle constructor. 
    '''
    def __init__(self, label, isDistinct=True):
        self.label = label
        self.isDistinct = isDistinct  
        self.prereqs = []
        self.conclusions = []
        self.z3Expr = Const(label, language.CircleSort)
        if self.isDistinct:
            self.conclusions.append(Distinct(self.z3Expr))
    
    def __eq__(self, other):
        if not isinstance(other, Circle):
            return False
        return self.z3Expr == other.z3Expr
    
    def __str__(self, *args, **kwargs):
        return "|Circle [" + str(self.z3Expr) + "] :\n" +\
                "|   prereq: " + str(self.prereqs) + "\n" + \
                "|   concls: " + str(self.conclusions) + "\n"
    
    
    def centerThrough(self, point1, point2):
        '''
        Specify construction place this circle with center point1
        and through point2
        '''
        self.prereqs.append(Not(point1.z3Expr == point2.z3Expr))
        self.conclusions.append(language.Center(point1.z3Expr, self.z3Expr))
        self.conclusions.append(language.OnCircle(point2.z3Expr, self.z3Expr))
        



        

yesNoFromSolverCheck = lambda x: 'yes' if x == 'sat' else 'no' 
boolFromSolverCheck = lambda x: True if x == 'sat' else False       
language = LanguageE()
solver = language.solver
