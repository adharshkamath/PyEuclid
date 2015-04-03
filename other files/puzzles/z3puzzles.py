"""

    This is dr.avigad's puzzles. I've made them friendly with python 3.4 .
    
"""


from z3 import * 


# Summers page 5
def puzzle1():

    Men, (Alec, Bill, Carl, Dave) = \
        EnumSort('Men', ('Alec', 'Bill', 'Carl', 'Dave'))

    Int = IntSort()
    tall = Function('tall', Men, Int)
    dark = Function('dark', Men, Int)
    handsome = Function('handsome', Men, Int)
    
    ideal = Const('ideal', Men)
    
    x = Const('x', Men)
    
    s = Solver()
    s.add(ForAll(x, Or(tall(x) == 0, tall(x) == 1)))
    s.add(ForAll(x, Or(dark(x) == 0, dark(x) == 1)))
    s.add(ForAll(x, Or(handsome(x) == 0, handsome(x) == 1)))
    s.add(tall(Alec) + tall(Bill) + tall(Carl) + tall(Dave) == 3)
    s.add(dark(Alec) + dark(Bill) + dark(Carl) + dark(Dave) == 2)
    s.add(handsome(Alec) + handsome(Bill) + handsome(Carl) + 
          handsome(Dave) == 1)
    s.add(ForAll(x, Or(tall(x) == 1, dark(x) == 1, handsome(x) == 1)))
    s.add(dark(Alec) == dark(Dave))    
    s.add(tall(Bill) == tall(Carl))
    s.add(tall(Carl) != tall(Dave))
    s.add(And(tall(ideal) == 1, dark(ideal) == 1, handsome(ideal) == 1))
    s.check()
    print (s.model())
    s.add(ideal != Alec)
    print (s.check())

# Summers page 7
def puzzle2():

    A, S, M, N = Ints('A S M N')
    variables = [A, S, M, N]
    s = Solver()
    for x in variables:
        s.add(x >= 0)
        s.add(x <= 9)
    for x in variables:
        for y in variables:
            if not(x is y):
                s.add(x != y)

    s.add((10 * A + S) * A == 100 * M + 10 * A + N)
    s.check()
    print (s.model())
    s.add(A != 8)
    print (s.check())

# Summers page 11
def puzzle3():
    
    People, (Alice, husband, son, daughter, brother) = \
        EnumSort('People', ('Alice', 'husband', 'son', 'daughter', 'brother'))

    Bool = BoolSort()
    withr = Function('with', People, People, Bool)
    male = Function('male', People, Bool)
    x, y = Consts('x, y', People)
    killer = Const('killer', People)
    victim = Const('victim', People)

    s = Solver()
    s.add(ForAll([x, y], Implies(withr(x, y), withr(y, x))))
    s.add(ForAll(x, Not(withr(x, x))))

    s.add(Not(male(Alice)))
    s.add(male(husband))
    s.add(male(son))
    s.add(Not(male(daughter)))
    s.add(male(brother))
    s.add(killer != victim)

    s.add(Exists([x, y], And(withr(x, y), male(x), Not(male(y)), x != killer,
                             y != killer, x != victim, y != victim)))
    s.add(withr(killer, victim))
    s.add(Or(ForAll(x, Not(withr(x, son))), 
             ForAll(x, Not(withr(x, daughter)))))
    s.add(Not(withr(Alice, husband)))
    s.add(husband != victim)

    print (s.check())
    print (s.model())

    s.add(husband != killer)

    print (s.check())
    print (s.model())

def asylum():

    People = DeclareSort('People')
    Bool = BoolSort()
    Doctor = Function('Doctor', People, Bool)
    Patient = Function('Patient', People, Bool)
    Peculiar = Function('Peculiar', People, Bool)
    Special = Function('Special', People, Bool)
    Sane = Function('Sane', People, Bool)
    best_friend = Function('best_friend', People, People)
    Tarr = Const('Tarr', People)
    Fether = Const('Tarr', People)
    x = Const('x', People)
    y = Const('y', People)

    hypotheses = [
        Doctor(Tarr),
        Doctor(Fether),
        ForAll(x, Doctor(x) == Not(Patient(x))),
        ForAll(x, Peculiar(x) == (Sane(x) == Patient(x))),
        ForAll(x, Special(x) == And(ForAll(y, Implies(Patient(y),
                                               Sane(y) == Peculiar(x))), 
                                    ForAll(y, Implies(Doctor(y),    
                                               Sane(y) == Not(Peculiar(x)))))),
        Exists(x, Sane(x)),
        ForAll([x, y], Implies(Sane(x) == Special(y), 
                               Sane(best_friend(x)) == Patient(y))), 
        Sane(Tarr) == ForAll(x, Implies(Doctor(x), Sane(x))),
        Sane(Tarr) == Exists(x, And(Patient(x), Sane(x))),
        Sane(Fether) == ForAll(x, Implies(Patient(x), Not(Sane(x)))),
        Sane(Fether) == Exists(x, And(Doctor(x), Sane(x))),
        Sane(Fether) == Sane(Tarr)
    ]

    conclusion = ForAll(x, And(Implies(Doctor(x), Not(Sane(x))),
                        Implies(Patient(x), Sane(x))))


    s = Solver()
    for h in hypotheses:
        s.add(h)
    s.add(Not(conclusion))
    print (s.check())
    
# lemma Problem13:
# assumes 
#   "Doctor Tarr" and 
#   "Doctor Fether" and 
#   "ALL x. Doctor x = (~ Patient x)" and
#   "ALL x. Peculiar x = (Sane x = Patient x)" and
#   "ALL x. Special x = ((ALL y. Patient y \<longrightarrow>
#     Sane y = Peculiar x) & (ALL y. Doctor y \<longrightarrow>
#     Sane y = (~ Peculiar x)))" and 
#   "EX x. Sane x" and
#   "ALL a b. (Sane a = Special b) \<longrightarrow> (Sane (best_friend a) = 
#     Patient b)" and
#   "Sane Tarr = (ALL x. Doctor x \<longrightarrow> Sane x)" and
#   "Sane Tarr = (EX x. Patient x & ~ Sane x)" and
#   "Sane Fether = (ALL x. Patient x \<longrightarrow> ~ Sane x)" and
#   "Sane Fether = (EX x. Doctor x & Sane x)" and
#   "Sane Fether = Sane Tarr"
# shows 
#   "ALL x. (Doctor x \<longrightarrow> ~ Sane x) & (Patient x \<longrightarrow> Sane x)"

#   using prems by metis

def kissing3():

    x = {}
    for i in range(2):
        for j in range(2):
            x[i,j] = Real('x{0}{1}'.format(i, j))

    s = Solver()
    for i in range(2):
        s.add(x[i,0] ** 2 + x[i,1] ** 2 == 4)
        s.add(x[i,1] >= 0)
        for j in range(i+1,2):
            s.add((x[i,0] - x[j,0]) ** 2 + (x[i,1] - x[j,1]) ** 2 >= 4)
        s.add((x[i,0] - 2) ** 2 + x[i,1] ** 2 >= 4)
        s.add((x[i,0] + 2) ** 2 + x[i,1] ** 2 >= 4)

    print ('Checking...')
    s.check()
    print (s.model())

def kissing2():

    x = {}
    for i in range(4):
        for j in range(2):
            x[i,j] = Real('x{0}{1}'.format(i, j))

    s = Solver()
    for i in range(4):
        s.add(x[i,0] ** 2 + x[i,1] ** 2 > 3.9)
        s.add(x[i,0] ** 2 + x[i,1] ** 2 < 4.1)
        for j in range(i+1,4):
            s.add((x[i,0] - x[j,0]) ** 2 + (x[i,1] - x[j,1]) ** 2 > 3.9)
        s.add((x[i,0] - 2) ** 2 + x[i,1] ** 2 > 3.9)
        s.add((x[i,0] + 2) ** 2 + x[i,1] ** 2 > 3.9)

    print ('Checking...')
    s.check()
    print (s.model())

def kissing():

    x = {}
    for i in range(4):
        for j in range(2):
            x[i,j] = Real('x{0}{1}'.format(i, j))

    s = Solver()
    for i in range(4):
        s.add(x[i,0] ** 2 + x[i,1] ** 2 == 4)
        for j in range(i+1,4):
            s.add((x[i,0] - x[j,0]) ** 2 + (x[i,1] - x[j,1]) ** 2 >= 3.9)
        s.add((x[i,0] - 2) ** 2 + x[i,1] ** 2 >= 3.9)
        s.add((x[i,0] + 2) ** 2 + x[i,1] ** 2 >= 3.9)

    print ('Checking...')
    s.check()
    print (s.model())




