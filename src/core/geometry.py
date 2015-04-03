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
    


        

