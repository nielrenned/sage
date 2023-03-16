from sage.rings.ring import CommutativeRing
from sage.rings.integer_ring import ZZ
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.categories.commutative_rings import CommutativeRings
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.padics.factory import Zp, Zq
from sage.rings.finite_rings.finite_field_constructor import GF

from sage.rings.polynomial.multi_polynomial import is_MPolynomial
from sage.rings.polynomial.polynomial_element import is_Polynomial

from .witt_vector import WittVector_base
from .witt_vector import WittVector_p_typical
from .witt_vector import WittVector_non_p_typical
from .witt_vector import _fcppow

from sage.sets.primes import Primes
_Primes = Primes()

class WittRing_base(CommutativeRing, UniqueRepresentation):
    
    Element = WittVector_base
    
    def __init__(self, base_ring, prec, prime, algorithm='none', category=None):
        self.prec = prec
        self.prime = prime
        
        self._algorithm = algorithm
        self.sum_polynomials = None
        self.prod_polynomials = None
        
        if algorithm == 'standard':
            self._generate_sum_and_product_polynomials(base_ring)
        
        if category is None:
            category = CommutativeRings()
        CommutativeRing.__init__(self, base_ring, category=category)
    
    def __iter__(self):
        from itertools import product, repeat
        for t in product(self.base(), repeat=self.prec):
            yield self(t)
    
    def _repr_(self):
        return f"Ring of Witt Vectors of length {self.prec} over {self.base()}"
    
    def _coerce_map_from_(self, S):
        # Question: do we return True is S == self.base()?
        # We have the teichmuller lift, but I don't think that's
        # a "coercion" map, per se.
        return (S is ZZ)
    
    def _element_constructor_(self, x):
        if x in ZZ:
            return self.element_class(self, self._int_to_vector(x))
        elif isinstance(x, tuple) or isinstance(x, list):
            return self.element_class(self, x)
        else:
            return NotImplemented
    
    def _int_to_vector(self, k):
        p = self.prime
        
        char = self.characteristic()
        if char != 0:
            k = k % char
        
        vec_k = [k]
        for n in range(1, self.prec):
            total = k - k**(p**n) - sum(p**(n-i) * vec_k[n-i]**(p**i) for i in range(1, n))
            total //= p**n
            vec_k.append(total)
        
        return vec_k
    
    def _generate_sum_and_product_polynomials(self, base):
        p = self.prime
        prec = self.prec
        x_var_names = ['X{}'.format(i) for i in range(prec)]
        y_var_names = ['Y{}'.format(i) for i in range(prec)]
        var_names = x_var_names + y_var_names
        
        # Okay, what's going on here? Sage, by default, relies on
        # Singular for Multivariate Polynomial Rings, but Singular uses
        # only SIXTEEN bits (unsigned) to store its exponents. So if we
        # want exponents larger than 2^16 - 1, we have to use the
        # generic implementation. However, after some experimentation,
        # it seems like the generic implementation is faster?
        #
        # After trying to compute S_4 for p=5, it looks like generic is
        # faster for  very small polys, and MUCH slower for large polys.
        # So we'll default to singular unless we can't use it.
        #
        # Remark: Since when is SIXTEEN bits sufficient for anyone???
        #
        if p**(prec-1) >= 2**16:
            implementation = 'generic'
        else:
            implementation = 'singular'
            
        # We first generate the "universal" polynomials and then project
        # to the base ring.
        R = PolynomialRing(ZZ, var_names, implementation=implementation)
        x_y_vars = R.gens()
        x_vars = x_y_vars[:prec]
        y_vars = x_y_vars[prec:]
        
        self.sum_polynomials = [0]*(self.prec)
        for n in range(prec):
            s_n = x_vars[n] + y_vars[n]
            for i in range(n):
                s_n += (x_vars[i]**(p**(n-i)) + y_vars[i]**(p**(n-i)) - self.sum_polynomials[i]**(p**(n-i))) / p**(n-i)
            self.sum_polynomials[n] = R(s_n)
        
        self.prod_polynomials = [x_vars[0] * y_vars[0]] + [0]*(self.prec)
        for n in range(1, prec):
            x_poly = sum([p**i * x_vars[i]**(p**(n-i)) for i in range(n+1)])
            y_poly = sum([p**i * y_vars[i]**(p**(n-i)) for i in range(n+1)])
            p_poly = sum([p**i * self.prod_polynomials[i]**(p**(n-i)) for i in range(n)])
            p_n = (x_poly*y_poly - p_poly) // p**n
            self.prod_polynomials[n] = p_n
        
        # We have to use generic here, because Singular doesn't support
        # Polynomial Rings over Polynomial Rings. For example,
        # ``PolynomialRing(GF(5)['x'], ['X', 'Y'], implementation='singular')``
        # will fail.
        S = PolynomialRing(base, x_y_vars, implementation='generic')
        for n in range(prec):
            self.sum_polynomials[n] = S(self.sum_polynomials[n])
            self.prod_polynomials[n] = S(self.prod_polynomials[n])
    
    def characteristic(self):
        p = self.prime
        if self.base()(p).is_unit():
            # If p is invertible, W_n(R) is isomorphic to R^n.
            return self.base().characteristic()
        else:
            # This is a conjecture. It's known for char(R) == p.
            return p**(self.prec-1) * self.base().characteristic()
    
    def precision(self):
        return self.prec
    
    def random_element(self):
        return self.element_class(self, tuple(self.base().random_element() for _ in range(self.prec)))
        
    def teichmuller_lift(self, x):
        if x not in self.base():
            raise Exception(f'{x} not in {self.base()}')
        else:
            return self.element_class(self, (x,) + tuple(0 for _ in range(self.prec-1)))
    
    def is_finite(self):
        return self.base().is_finite()
    
    def cardinality(self):
        return self.base().cardinality()**(self.prec)


class WittRing_p_typical(WittRing_base):
    
    Element = WittVector_p_typical
    
    def __init__(self, base_ring, prec, prime, algorithm=None, category=None):
        WittRing_base.__init__(self, base_ring, prec, prime,
                               algorithm=algorithm, category=category)
        
        if algorithm == 'finotti':
            self.generate_binomial_table()
    
    def _int_to_vector(self, k):
        p = self.prime
        R = Zp(p, prec=self.prec+1, type='fixed-mod')
        F = GF(p)
        B = self.base()
        
        series = R(k)
        witt_vector = []
        for _ in range(self.prec):
            # Probably slightly faster to do "series % p," but this way, temp is in F_p
            temp = F(series)
            witt_vector.append(B(temp)) # make sure elements of vector are in base
            series = (series - R.teichmuller(temp)) // p
        return witt_vector
    
    def generate_binomial_table(self):
        import numpy as np
        p = self.prime
        R = Zp(p, prec=self.prec+1, type='fixed-mod')
        v_p = ZZ.valuation(p)
        table = [[0]]
        for k in range(1, self.prec+1):
            row = np.empty(p**k, dtype=int)
            row[0] = 0
            prev_bin = 1
            for i in range(1, p**k // 2 + 1):
                val = v_p(i)
                # Instead of calling binomial each time, we compute the coefficients
                # recursively. This is MUCH faster.
                next_bin = prev_bin * (p**k - (i-1)) // i
                prev_bin = next_bin
                series = R(-next_bin // p**(k-val))
                for _ in range(val):
                    temp = series % p
                    series = (series - R.teichmuller(temp)) // p
                row[i] = ZZ(series % p)
                row[p**k - i] = row[i] # binomial coefficients are symmetric
            table.append(row)
        self.binomial_table = table
    
    def eta_bar(self, vec, eta_index):
        vec = tuple(x for x in vec if x != 0) # strip zeroes
        
        # special cases
        if len(vec) <= 1:
            return 0
        if eta_index == 0:
            return sum(vec)
        
        # renaming to match notation in paper
        k = eta_index
        p = self.prime
        # if vec = (x,y), we know what to do: Theorem 8.6
        if len(vec) == 2:
            # Here we have to check if we've pre-computed already
            x, y = vec
            scriptN = [[None] for _ in range(k+1)] # each list starts with None, so that indexing matches paper
            # calculate first N_t scriptN's
            for t in range(1, k+1):
                for i in range(1, p**t):
                    scriptN[t].append(self.binomial_table[t][i] * _fcppow(x, i) * _fcppow(y, p**t - i))
            indexN = [p**i - 1 for i in range(k+1)]
            for t in range(2, k+1):
                for l in range(1, t):
                    # append scriptN_{t, N_t+l}
                    next_scriptN = self.eta_bar(scriptN[t-l][1:indexN[t-l]+t-l], l)
                    scriptN[t].append(next_scriptN)
            return sum(scriptN[k][1:])
        
        # if vec is longer, we split and recurse: Proposition 5.4
        # This is where we need to using multiprocessing.
        else:
            m = len(vec) // 2
            v_1 = vec[:m]
            v_2 = vec[m:]
            s_1 = sum(v_1)
            s_2 = sum(v_2)
            total = 0
            scriptM = [[] for _ in range(k+1)]
            for t in range(1, k+1):
                scriptM[t].append(self.eta_bar(v_1,        t))
                scriptM[t].append(self.eta_bar(v_2,        t))
                scriptM[t].append(self.eta_bar((s_1, s_2), t))
            for t in range(2, k+1):
                for s in range(1, t):
                    result = self.eta_bar(scriptM[t-s], s)
                    scriptM[t].append(result)
            return sum(scriptM[k])


class WittRing_finite_field(WittRing_p_typical):
    def __init__(self, base_ring, prec, prime, category=None):
        WittRing_p_typical.__init__(self, base_ring, prec, prime,
                                    algorithm='Zq_isomorphism',
                                    category=category)
    
    def _series_to_vector(self, series):
        F = self.base() # known to be finite
        R = Zq(F.cardinality(), prec=self.prec, type='fixed-mod', modulus=F.polynomial(), names=['z'])
        K = R.residue_field()
        p = self.prime
        
        series = R(series)
        witt_vector = []
        for i in range(self.prec):
            temp = K(series)
            elem = temp.polynomial()(F.gen()) # hack to convert to F (K != F for some reason)
            witt_vector.append(elem**(p**i))
            series = (series - R.teichmuller(temp)) // p
        return witt_vector
    
    def _vector_to_series(self, vec):
        F = self.base()
        R = Zq(F.cardinality(), prec=self.prec, type='fixed-mod', modulus=F.polynomial(), names=['z'])
        K = R.residue_field()
        p = self.prime
        
        series = R(0)
        for i in range(0, self.prec):
            temp = vec[i].nth_root(p**i)
            elem = temp.polynomial()(K.gen()) # hack to convert to K (F != K for some reason)
            series += p**i * R.teichmuller(elem)
        return series


class WittRing_non_p_typical(WittRing_base):
    
    Element = WittVector_non_p_typical
    
    def __init__(self, base_ring, prec, prime, algorithm=None, category=None):
        WittRing_base.__init__(self, base_ring, prec, prime,
                               algorithm=algorithm, category=category)
    
    def _repr_(self):
        return f"Ring of {self.prime}-Witt Vectors of length {self.prec} over {self.base()}"


class WittRing_integers(WittRing_non_p_typical):
    def __init__(self, prec, prime, category=None):
        WittRing_base.__init__(self, ZZ, prec, prime,
                               algorithm='ghost_map_isomorphism',
                               category=category)
    
    def _coefficients_to_vector(self, c):
        p = self.prime
        v = []
        for n in range(self.prec):
            v.append((c[n] - sum(p**i *v[i]**(p**(n-i)) for i in range(n))) / p**n)
        return v
    
    def _vector_to_coefficients(self, v):
        p = self.prime
        return tuple(sum(p**i * v.vec[i]**(p**(n-i)) for i in range(n+1)) for n in range(self.prec))


class WittRing_integers_mod_power_of_p(WittRing_non_p_typical):
    def __init__(self, base_ring, prec, prime, category=None):
        self.alpha = ZZ.valuation(prime)(base_ring.characteristic())
        WittRing_base.__init__(self, base_ring, prec, prime,
                               algorithm='IntegerMod_isomorphism',
                               category=category)
    
    def _coefficients_to_vector(self, c):
        p = self.prime
        n = self.prec
        alpha = self.alpha
        
        B = self.base()
        R = Zmod(p**(alpha+n-1))
        
        v = []
        for i in range(n-1):
            # It may appear that we can simplify the computations below
            # by canceling common factors in the multiplication and
            # division. However, since the first computations are done in
            # R and then we switch to ZZ, this cancellation doesn't work.
            v_i = R(c[0]) + p**(i+1)*R(c[i+1])
            v_i -= sum(p**j * R(v[j])**(p**(i-j)) for j in range(i))
            v_i *= p**(n-i-1)
            v_i = ZZ(v_i) // p**(n-1)
            v.append(B(v_i))
        
        last_v = R(c[0]) - sum(p**j * R(v[j])**(p**(n-j-1)) for j in range(n-1))
        last_v = ZZ(last_v) // p**(n-1)
        v.append(B(last_v))
        
        return tuple(v)
    
    def _vector_to_coefficients(self, v):
        p = self.prime
        n = self.prec
        alpha = self.alpha
        
        R = Zmod(p**(alpha+n-1))
        S = Zmod(p**(alpha-1))
        
        c0 = sum(p**j * R(v.vec[j])**(p**(n-j-1)) for j in range(n))
        c = [c0]
        for i in range(1, n):
            # It may appear that we can simplify the computations below
            # by canceling common factors in the multiplication and
            # division. However, since the first computations are done in
            # R and then we switch to ZZ, this cancellation doesn't work.
            c_i = sum(p**j * R(v.vec[j])**(p**(i-j-1)) for j in range(i)) - c0
            c_i *= p**(n-i)
            c_i = ZZ(c_i) // p**n
            c.append(S(c_i))
        
        return tuple(c)


class WittRing_p_invertible(WittRing_non_p_typical):
    def __init__(self, base_ring, prec, prime, category=None):
        WittRing_non_p_typical.__init__(self, base_ring, prec, prime,
                                        algorithm='standard_otf',
                                        category=category)
