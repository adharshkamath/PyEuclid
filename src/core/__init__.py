from core.LanguageE import LanguageE
from z3 import Solver, Consts, Not, eq, Distinct, simplify



    
if __name__ == '__main__':
    
    print "=== Loading Core ==="    
    language = LanguageE()
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

    
    
    
    
    
    
    
    
    
    