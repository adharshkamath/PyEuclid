from enum import Enum
'''
Created on Mar 27, 2015

@author: krojas
'''
from sets import Set


class GeometricObject(Enum):
    '''
    classdocs
    '''
    POINT = 0
    LINE = 1
    CIRCLE = 2
    SEGMENT = 3
    ANGLE = 4
    AREA = 5
    
    
class AbstractGeometricObject(object):
    
    def __init__(self, name):
        self.name = name
    
    def draw(self):
        print self.name
        
        
class Point(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.POINT
    

class Circle(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.CIRCLE
        
class Line(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.LINE
    
class Segment(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.SEGMENT

class Angle(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.ANGLE

class Area(AbstractGeometricObject):
    
    def __init__(self, name):
        super.__init__(self, name)
        self.type = GeometricObject.AREA
    


class ConstructionRuleType(Enum):
    DISTINCT = (ConstructionRules.pointDistinct, "distinct")
    ON = (ConstructionRules.on, "on",)
    BETWEEN = (ConstructionRules.between, "between")
    INTERSECTION = (ConstructionRules.intersect, "intersection")
    def __init__(self, pMethod, pKeyWord):
        self.method = pMethod
        self.rulename = pKeyWord
    def rulename(self):
        return self.rulename
    def __method(self):
        return self.method

class ConstructionRules(object):
    
    def distinct(solver, diagram, geometric_object):  # @NoSelf
        '''
        [x is distinct from]
        REQUIRES: true
        ENSURES: [x is distinct from ...]
        :param solver:
        :param diagram:
        :param geometric_object: a geometric object
        '''
        return (False, diagram)
    
    def on(solver, diagram, geometric_object1, geometric_object2):  # @NoSelf
        '''
        [a is on b]
        REQUIRES: b is distinct
        ENSURES: a is distinct and on b
        '''
        
        ## TODO: check type of geometric_object
        return (False, diagram)
    
    def between(self, diagram, geometric_object1, geometric_object_2, geometric_object_3):
        '''
        [b is between a and c
        REQUIRES:
        ENSURES:
        '''
        return (False, diagram)
    
    def intersection(self, diagram, geometric_object1, geometric_object2):
        '''
        blah
        REQUIRES:
        ENSURES:
        '''
        return (False, diagram)
        
        

