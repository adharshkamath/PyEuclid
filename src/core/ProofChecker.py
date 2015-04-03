'''
Created on Apr 2, 2015

@author: krojas
'''
from core import LanguageE
import sets
import z3
from z3 import *

class ProofChecker(object):
    '''
    classdocs
    '''


    def __init__(self, language):
        '''
        Constructor
        '''
        print "=== Initializing proof checker ==="
        self.language = language
        self.solver = language.solver
        
        self.points = sets.Set()
        self.lines = sets.Set()
        self.circles = sets.Set()
        self.assumptions = sets.Set()
        self.conclusions = sets.Set()
        
        
        
        
    ## TODO: implement parsing methods    
    def assertConstructionRule(self, arg=""):
        return None       
        
    def assertTheorem(self, theorem=None):
        return None
        
    
    def createPoints(self, args):
        
        
        
    
