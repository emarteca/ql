
class Iterator:
        #Support both 2 and 3 protocol

        def __next__(self):
            pass

        def next(self):
            pass

        def __iter__(self):
            return self

class X(object):

    def __iter__(self):
        return object()


#Iterator not returning self

class AlmostIterator(object):

    def __next__(self):
        pass

    def next(self):
        pass

    def __iter__(self):
        return X.Xiter(X())

class AlmostIterable(object):

    def __iter__(self):
        return AlmostIterator()

#Overly complex __del__ method

class MegaDel(object):

    def __del__(self):
        a = self.x + self.y
        if a:
            print(a)
        if sys._getframe().f_lineno > 100:
            print("Hello")
        sum = 0
        for a in range(100):
            sum += a
        print(sum)

class MiniDel(object):

    def close(self):
        pass

    def __del__(self):
        self.close()
        
class IncorrectSpecialMethods(object):
    
    def __add__(self, other):
        raise NotImplementedError()
    
    def __getitem__(self, index):
        raise ZeroDivisionError()
        
    def __getattr__(self):
        raise ZeroDivisionError()
    
def f(self):
    pass
    
class MissingMethods(object):
    
    __repr__ = f # This should be OK
    __add__ = f # But not this
    __set__ = f # or this
    
#OK Special method
class OK(object):
    
    def __call__(self):
        yield 0
        raise StopIteration

        
        
        
