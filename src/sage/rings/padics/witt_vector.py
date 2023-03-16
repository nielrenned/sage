from sage.structure.element import CommutativeRingElement
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.padics.factory import Zq
from sage.rings.integer_ring import ZZ

from sage.rings.polynomial.multi_polynomial import is_MPolynomial
from sage.rings.polynomial.polynomial_element import is_Polynomial

from sage.sets.primes import Primes
_Primes = Primes()

def _fast_char_p_power(x, n, p=None):
    r"""
    Raise x^n power in characteristic p
    
    If x is not an element of a ring of characteristic p, throw an error.
    If x is an element of GF(p^k), this is already fast.
    However, is x is a polynomial, this seems to be slow?
    """
    if n not in ZZ:
        raise ValueError(f'Exponent {n} is not an integer')
    if n == 0 or x == 1:
        return x.parent().one()
    if x.parent().characteristic() not in _Primes:
        raise ValueError(f'{x} is not in a ring of prime characteristic')
    
    x_is_Polynomial = is_Polynomial(x)
    x_is_MPolynomial = is_MPolynomial(x)
    
    if not (x_is_Polynomial or x_is_MPolynomial):
        return x**n
    if (x_is_Polynomial and x.is_gen()) or (x_is_MPolynomial and x.is_generator()):
        return x**n
    if n < 0:
        x = x**-1  # This may throw an error.
        n = -n
    
    P = x.parent()
    if p is None:
        p = P.characteristic()
    base_p_digits = ZZ(n).digits(base=p)
    
    x_to_the_n = 1
    
    for p_exp, digit in enumerate(base_p_digits):
        if digit == 0:
            continue
        inner_term = x**digit
        term_dict = {}
        for e_int_or_tuple, c in inner_term.dict().items():
            power = p**p_exp
            new_c = _fast_char_p_power(c, power)
            new_e_tuple = None
            if x_is_Polynomial:  # Then the dict keys are ints
                new_e_tuple = e_int_or_tuple * power
            elif x_is_MPolynomial:  # Then the dict keys are ETuples
                new_e_tuple = e_int_or_tuple.emul(power)
            term_dict[new_e_tuple] = new_c
        term = P(term_dict)
        x_to_the_n *= term
    
    return x_to_the_n


_fcppow = _fast_char_p_power

class WittVector_base(CommutativeRingElement):
    def __init__(self, parent, vec=None):
        self.prec = parent.precision()
        B = parent.base()
        if vec is not None:
            if len(vec) != self.prec:
                raise ValueError(f'{vec} is not the correct length. Expected length to be {self.prec}.')
            self.vec = tuple(B(x) for x in vec)
        else:
            self.vec = (B(0) for i in range(self.prec))
        CommutativeRingElement.__init__(self, parent)
    
    def __hash__(self):
        return hash(self.vec)
    
    def _richcmp_(self, other, op):
        from sage.structure.richcmp import op_EQ, op_NE
        if op == op_EQ:
            return self.vec == other.vec
        elif op == op_NE:
            return self.vec != other.vec
        else:
            return NotImplemented
    
    def _repr_(self):
        return '(' + ', '.join(map(str, self.vec)) + ')'
    
    def _add_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if other == P.zero():
            return self
        elif self == P.zero():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            s = P.sum_polynomials
            # note here this is tuple addition, i.e. concatenation
            sum_vec = tuple(s[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=sum_vec)
        else:
            return NotImplemented
    
    def _mul_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero or one ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if self == P.zero() or other == P.zero():
            return P.zero()
        elif other == P.one():
            return self
        elif self == P.one():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            p = P.prod_polynomials
            # note here this is tuple addition, i.e. concatenation
            prod_vec = tuple(p[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=prod_vec)
        else:
            return NotImplemented
    
    def _neg_(self):
        P = self.parent()
        C = self.__class__
        # If p == 2, -1 == (-1, -1, -1, ...)
        # Otherwise, -1 == (-1, 0, 0, ...)
        if P.prime == 2:
            all_ones = P(tuple(-1 for _ in range(self.prec)))
            return all_ones*self
        neg_vec = tuple(-self.vec[i] for i in range(self.prec))
        return C(P, vec=neg_vec)
    
    def _div_(self, other):
        P = self.parent()
        # As a slight optimization, we'll check for one ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if other == P.one():
            return self
        elif self == P.one():
            return other._invert_()
        
        return self * other._invert_()
    
    def _invert_(self):
        if not self.vec[0].is_unit():
            raise ZeroDivisionError(f"Inverse of {self} does not exist.")
        P = self.parent()
        C = self.__class__
        
        if self == P.one():
            return self
        if self.prec == 1:
            return P((self.vec[0]**-1, ))
        
        # Strategy: Multiply ``self`` by ``(Y_0, Y_1, ...)``, set equal
        # to (1, 0, 0, ...), and solve.
        var_names = [f'Y{i}' for i in range(1, self.prec)]
        poly_ring = PolynomialRing(P.base(), var_names)
        inv_vec = list((self.vec[0]**-1, ) + poly_ring.gens()) # We'll fill this in one-by-one
        
        from sage.rings.padics.witt_ring_constructor import WittRing
        W = WittRing(poly_ring, p=P.prime, prec=P.prec)
        prod_vec = (W(self.vec)*W(inv_vec)).vec
        for i in range(1, self.prec):
            poly = prod_vec[i](inv_vec[1:])
            Y_i = poly.parent().gens()[i-1]
            inv_vec[i] = -poly.constant_coefficient() / poly.monomial_coefficient(Y_i)
        
        return C(P, vec=inv_vec)


class WittVector_p_typical(WittVector_base):
    def _add_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if other == P.zero():
            return self
        elif self == P.zero():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            s = P.sum_polynomials
            # note here this is tuple addition, i.e. concatenation
            sum_vec = tuple(s[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=sum_vec)
        elif alg == 'finotti':
            x = self.vec
            y = other.vec
            prec = P.precision()
            p = P.prime
            bin_table = P.binomial_table
            
            G = []
            for n in range(0, prec):
                G_n = [x[n], y[n]]
                for i in range(0, n):
                    G_n.append(P.eta_bar(G[i], n-i))
                G.append(G_n)
            sum_vec = tuple(sum(G[i]) for i in range(prec))
            return C(P, vec=sum_vec)
        elif alg == 'Zq_isomorphism':
            x = P._vector_to_series(self.vec)
            y = P._vector_to_series(other.vec)
            sum_vec = P._series_to_vector(x+y)
            return C(P, vec=sum_vec)
        else:
            return NotImplemented
    
    def _mul_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero or one ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if self == P.zero() or other == P.zero():
            return P.zero()
        elif other == P.one():
            return self
        elif self == P.one():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            p = P.prod_polynomials
            # note here this is tuple addition, i.e. concatenation
            prod_vec = tuple(p[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=prod_vec)
        elif alg == 'finotti':
            x = self.vec
            y = other.vec
            prec = P.precision()
            p = P.prime
            bin_table = P.binomial_table
            
            G = [[x[0] * y[0]]]
            for n in range(1, prec):
                G_n = [_fcppow(x[0], p**n) * y[n], _fcppow(y[0], p**n) * x[n]]
                G_n.extend(_fcppow(x[i], p**(n-i)) * _fcppow(y[n-i], p**i) for i in range(1, n))
                for i in range(0, n):
                    G_n.append(P.eta_bar(G[i], n-i))
                G.append(G_n)
            prod_vec = tuple(sum(G[i]) for i in range(prec))
            return C(P, vec=prod_vec)
        elif alg == 'Zq_isomorphism':
            x = P._vector_to_series(self.vec)
            y = P._vector_to_series(other.vec)
            sum_vec = P._series_to_vector(x*y)
            return C(P, vec=sum_vec)
        else:
            return NotImplemented


class WittVector_non_p_typical(WittVector_base):
    
    def _add_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if other == P.zero():
            return self
        elif self == P.zero():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            s = P.sum_polynomials
            # note here this is tuple addition, i.e. concatenation
            sum_vec = tuple(s[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=sum_vec)
        elif alg == 'standard_otf':
            p = P.prime # we know p is a unit in this case!
            x = self.vec
            y = other.vec
            
            sum_vec = [x[0] + y[0]]
            for n in range(1, self.prec):
                next_sum = x[n] + y[n] + \
                    sum((x[i]**(p**(n-i)) + y[i]**(p**(n-i)) - sum_vec[i]**(p**(n-i))) / p**(n-i)
                        for i in range(0, n))
                sum_vec.append(next_sum)
            
            return C(P, vec=sum_vec)
        elif alg == 'IntegerMod_isomorphism' or alg == 'ghost_map_isomorphism':
            a = P._vector_to_coefficients(self)
            b = P._vector_to_coefficients(other)
            sum_coeffs = tuple(a[i] + b[i] for i in range(self.prec))
            return C(P, vec=P._coefficients_to_vector(sum_coeffs))
        else:
            return NotImplemented
    
    def _mul_(self, other):
        P = self.parent()
        C = self.__class__
        
        # As a slight optimization, we'll check for zero or one ahead of time.
        # This has the benefit of allowing us to create polynomials,
        # even if ``P._algorithm`` is 'none'.
        if self == P.zero() or other == P.zero():
            return P.zero()
        elif other == P.one():
            return self
        elif self == P.one():
            return other
        
        alg = P._algorithm
        if alg == 'standard':
            p = P.prod_polynomials
            # note here this is tuple addition, i.e. concatenation
            prod_vec = tuple(p[i](*(self.vec + other.vec)) for i in range(self.prec))
            return C(P, vec=prod_vec)
        elif alg == 'standard_otf':
            p = P.prime # we know p is a unit in this case!
            x = self.vec
            y = other.vec
            
            prod_vec = [x[0] * y[0]]
            for n in range(1, self.prec):
                next_prod = (
                    sum(p**i * x[i]**(p**(n-i)) for i in range(0, n+1)) *
                    sum(p**i * y[i]**(p**(n-i)) for i in range(0, n+1)) -
                    sum(p**i * prod_vec[i]**(p**(n-i)) for i in range(0, n))
                ) / p**n
                prod_vec.append(next_prod)
            
            return C(P, vec=prod_vec)
        elif alg == 'IntegerMod_isomorphism':
            p = P.prime
            
            a = P._vector_to_coefficients(self)
            b = P._vector_to_coefficients(other)
            
            prod_coeffs = [a[0]*b[0]]
            for i in range(1, self.prec):
                c_i = a[0]*b[i] + a[i]*b[0] + p**i * a[i]*b[i]
                prod_coeffs.append(c_i)
            
            return C(P, vec=P._coefficients_to_vector(prod_coeffs))
        elif alg == 'ghost_map_isomorphism':
            a = P._vector_to_coefficients(self)
            b = P._vector_to_coefficients(other)
            prod_coeffs = tuple(a[i] * b[i] for i in range(self.prec))
            return C(P, vec=P._coefficients_to_vector(prod_coeffs))
        else:
            return NotImplemented
