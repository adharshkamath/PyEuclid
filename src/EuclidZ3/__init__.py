from z3 import Solver, Consts, Not, eq, Distinct, simplify, is_const, Exists
from EuclidZ3.core import *
 

 
def test1():   
    print "=== Loading Core ==="    
    
    solver = Solver()
    solver.push()
    solver.add(language.axioms)
 
    print "=== Starting tests ==="
    
    
    print ">> Let p q r s t u v be distinct points"
    p, q, r, s, t, u, v = Consts('p q r s t u v', language.PointSort)
    solver.add(simplify(Distinct(p,q,r,s,t,u,v), blast_distinct=True))
    
    
    print ">> Let L M N O be distinct lines"
    K, L, M, N, O = Consts('K L M N O', language.LineSort)
    solver.add(simplify(Distinct(K,L,M,N,O), blast_distinct=True))
    
    
    ## Diagram description 
    assumptions = []
     
    assumptions.append(language.OnLine(p,L))
    assumptions.append(language.OnLine(q,L))
    assumptions.append(language.OnLine(p,N))
    assumptions.append(language.OnLine(s,N))
    assumptions.append(language.OnLine(t,N))
    assumptions.append(language.OnLine(p,M))
    assumptions.append(language.OnLine(r,M))
    assumptions.append(language.OnLine(q,O))
    assumptions.append(language.OnLine(s,O))
    assumptions.append(language.OnLine(r,O))
    assumptions.append(language.OnLine(q,K))
    assumptions.append(language.OnLine(t,K))
    assumptions.append(Not(language.OnLine(r,L)))
    assumptions.append(language.Between(p,s,t))
    assumptions.append(language.Between(q,s,r))
    assumptions.append(language.Between(s,u,t))
    assumptions.append(Not(p == q))
    assumptions.append(language.Between(p,q,v))
  
    
    
    print ">> Assume " + str(assumptions)
    solver.add(assumptions)
    print "      << z3: " + str(solver.check())
     
     
    ## Satisfied 
    solver.push()
    solver.add(True)
    print ">> Hence True"    
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## Satisfied  
    solver.push()
    solver.add(Not(language.SameSide(s,t,O)))
    print ">> Hence s and t are on opposite sides of O"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## Satisfied  
    solver.push()
    solver.add(language.SameSide(u,t,M))
    print ">> Hence u and t are on same side of M"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(language.SameSide(p,t,O))
    print ">> Hence p and t are on same side of O"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(language.SameSide(s,t,O))
    print ">> Hence s and t are on same side of O"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(Not(language.SameSide(s,t,M)))
    print ">> Hence s and t are on opposite sides of M"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(Not(language.SameSide(u,t,M)))
    print ">> Hence u and t are on opposite sides of M"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(language.Between(s,p,t))
    print ">> Hence p is between s and t"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(M == N)
    print ">> Hence p is between s and t"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(language.Between(q,s,u))
    print ">> Hence s is between q and u"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(Not( language.Segment(s,u) < language.Segment(s,t)))
    print ">> Hence seg su is less than seg st"
    print "      << z3: " + str(solver.check())
    solver.pop()
    
    ## unsatisfied  
    solver.push()
    solver.add(L==K)
    print ">> Hence L = K"
    print "      << z3: " + str(solver.check())
    solver.pop()

 
 
 
def testPointConstructions():
    """
    This test serves as an example of various constructions.
    In the absence of a way of checking equality of z3 objects,
    this test prints the prereqs and conclusions of constructions rules.
    We can then check these by eye for correct pre and post requirements.
    
    This is independent of the proof checker checking/asserting
    those requirements to Z3.
    
    Each corresponds to pages 715-717 of "A Formal System For Euclid's Elements"
    by Avigad et al.
    """
    
    print "\n=== testPointConstruction ==="
    print "> let p be a distinct point"
    p = Point("p")
    print str(p)  
    
    print "> let p be a non-distinct point"
    p = Point("p",False)
    print str(p)  
    
    print "> let p be a point on L"
    L = Line('L')
    p = Point('p')
    p.onLine(L)
    print str(p)
    
    print "> let p be a point on L between b and c"
    L = Line('L')
    p = Point('p')
    p.onLine(L)
    b = Point('b')
    b.onLine(L)
    c = Point('c')
    c.onLine(L)
    p.between(b,c)
    print str(b)
    print str(c)
    print str(p)
    
    
    print '> let p be a point on L extending the segment from b to c'
    ## TODO: for avigad: this example shows that although the point p
    ## doesn't have all of the conclusions and prerequisites listed
    ## when the points b, c, and the line L are passed to the proof checker,
    ## collectively their prereqs and conclusions are exactly those listed
    ## by the construction rule 4, pg 716.
    b = Point('b')
    c = Point('c')
    L = Line('L')
    b.onLine(L)
    c.onLine(L)
    p = Point('p')
    p.onLine(L)
    c.between(b, p)
    print str(p)
    print str(c)
    print str(b)
    
    print '> let p be a point on the same side of L as b'
    p = Point('p')
    b = Point('b')
    L = Line('L')
    p.sameside(b, L)
    print str(p)
    
    print '> let p be a point on the side L opposite b'
    b = Point('b')
    L = Line('L')
    p = Point('p')
    p.opposite(b, L)
    print str(p)
    
    print '> let p be a point on circle alpha'
    p = Point("p")
    alpha = Circle("alpha")
    p.onCircle(alpha)
    print str(p)
    print str(alpha)
    
    
    print '> let p be a point inside circle alpha'
    alpha = Circle("alpha")
    p = Point("p")
    p.inside(alpha)
    print str(p)
    print str(alpha)
    
    print '> let p be a point outside circle alpha'
    alpha = Circle("alpha")
    p = Point("p")
    p.outside(alpha)
    print str(p)
    
    
def testLinesAndCircles():
    """
    This test checks that construction rules for lines and circles
    list correct pre and post requirements. This test is also an example
    of how to use this framework.
    
    Each corresponds to pages 715-717 of "A Formal System For Euclid's Elements"
    by Avigad et al.
    """
    
    print "\n=== testLinesAndCirclesConstruction ==="    
    print "> let L be the line through a and b"
    L = Line("L")
    a = Point("a")
    b = Point("b")
    L.through(a,b)
    print str(L)
    
    print "> let alpha be the circle with center a passing through b"
    a = Point("a")
    b = Point("b")
    alpha = Circle("alpha")
    alpha.centerThrough(a, b)
    print str(alpha)
    
def testIntersections():
    """
    This test checks that construction rules for lines and circles
    list correct pre and post requirements. This test is also an example
    of how to use this framework.
    
    Each corresponds to pages 715-717 of "A Formal System For Euclid's Elements"
    by Avigad et al.
    """
    
    print "=== testIntersections ==="
    print ">let a be the intersection of L and M"
    a = Point("a")
    L = Line("L")
    M = Line("M")
    a.intersectsLines(L, M)
    print str(a)
    
    print ">let a be a point of intersection of circle alpha and line L"
    a = Point("a")
    L = Line("L")
    alpha = Circle("alpha")
    a.intersectsCircleLine(alpha, L)
    print str(a)
    
    print ">let a and b be the two points of intersection of circle alpha and line L"
    ## TODO: check with avigad
    a = Point("a")
    b = Point("b")
    L = Line("L")
    alpha = Circle("alpha")
    a.intersectsCircleLine(alpha, L)
    b.intersectsCircleLine(alpha, L)
    print str(a)
    print str(b)
    
    print ">let a be the point of intersection of L and circle alpha between b and c."
    a = Point("a")
    b = Point("b")
    c = Point("c")
    alpha = Circle("alpha")
    L = Line("L")
    a.intersectsCircleLine(alpha, L)
    a.between(b, c)
    print a
    
    print ">let a be the point of intersection of L and circle alpha extending the segment from c to b"
    ## TODO: ask avigad for picture
    
    print ">let a be a point on the intersection of alpha and beta"
    a = Point("a")
    alpha = Circle("alpha")
    beta = Circle("beta")
    a.intersectsCircleCircle(alpha,beta)
    print a
    
    print ">let a and b be the two points of intersection of alpha and beta"
    ## TODO: is this what avigad has in mind? Is what matters the prereqs and conclusions?
    a = Point("a")
    b = Point("b")
    alpha = Circle("alpha")
    beta = Circle("beta")
    a.intersectsCircleCircle(alpha, beta)
    b.intersectsCircleCircle(alpha, beta)
    print str(a)
    print str(b)    
       
def testProofCheckerConstruction1():
    '''
    This test works with the proof checker
    to prove that if some line L and M both go through 2 points
    a and b, then those two lines are the same.
    '''
    print "=== testProofCheckerConstruction1 ==="
    
    pc = Proofchecker()
    print "> before construction"
    print pc.status()
    print "> let a be a distinct point"
    a = Point("a")
    pc.construct(a)
    print "> let b be a distinct point"
    b = Point("b")
    pc.construct(b)
    print "> let L be a distinct line through a and b"
    L = Line("L")
    L.through(a,b)
    pc.construct(L)
    print "> after constructions"
    print pc.status()
    print "> hence a == b "
    pc.hence(a == b)
    print "> let m be the line through a and b"
    M = Line("M")
    M.through(a,b)
    pc.construct(M)
    print "> hence M == L"
    pc.hence(L == M)
    print pc.status()
    print "> hence M does not intersect L"
    ## TODO: make it so that you don't have to type language.*
    ## and so that functions like Intersectsll can take
    ## Geometric objects like Line instead of z3expression
    pc.hence(Not(language.Intersectsll(L.z3Expr,M.z3Expr)))
    
    
    

def testZ3Distinctness():
    '''
    This test is simply a playground to explore
    how z3 handles distinctness and equality checking.
    '''
    s = Solver()
    x, y = Consts('x y', language.PointSort)
    s.add(Distinct(x))   
    s.add(Distinct(y))
    print s
#     print s.add(Not(eq(x,y)))
#     print eq(simplify(x),simplify(y))
#     s.add(eq(x,y))
    s.add(Not(eq(x,y)))
    print s.check()
    print s
         


if __name__ == '__main__':
    print "\n=== Running Tests for EuclidZ3 ==="
#     test1()
#     testZ3Distinctness()
#     testPointConstructions()
    testLinesAndCircles()
#     testIntersections()
    testProofCheckerConstruction1()
    
    
    
    
    
    
    