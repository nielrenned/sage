"""
Root system data for type Q
"""
#*****************************************************************************
#       Copyright (C) 2018 Wencin Poh
#       Copyright (C) 2018 Anne Schilling
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import print_function
from __future__ import absolute_import


from .cartan_type import CartanType_standard_finite
from sage.combinat.root_system.root_system import RootSystem

class CartanType(CartanType_standard_finite):
    """
    Cartan Type `Q_n`

    .. SEEALSO:: :func:`~sage.combinat.root_systems.cartan_type.CartanType`
    """
    def __init__(self, n):
        """
        EXAMPLES::

            sage: ct = CartanType(['Q',4])
            sage: ct
            ['Q', 4]
            sage: ct._repr_(compact = True)
            'Q4'

            sage: ct.is_irreducible()
            True
            sage: ct.is_finite()
            True
            sage: ct.is_affine()
            False
            sage: ct.is_crystallographic()
            True
            sage: ct.is_simply_laced()
            True
            sage: ct.affine()
            ['Q', 4, 1]
            sage: ct.dual()
            ['Q', 4]

        TESTS::

            sage: TestSuite(ct).run()
        """
        assert n >= 0
        CartanType_standard_finite.__init__(self, "Q", n)

    def index_set(self):
        """
        Returns index set for Cartan type Q.

        The index set for type Q is of the form
        `\{-n, \ldots, -1, 1, \ldots, n\}`.

        EXAMPLES::

            sage: CartanType(['Q', 2]).index_set()
            (1, 2, -2, -1)
        """
        return tuple(range(1,self.n+1)+range(-self.n,0))

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: latex(CartanType(['Q',4]))
            Q_{4}
        """
        return "Q_{%s}"%self.n

    def root_system(self):
        """
        Return the root system of ``self``.

        EXAMPLES::

            sage: Q = CartanType(['Q',3])
            sage: Q.root_system()
            Root system of type ['A', 3]
        """
        return RootSystem(['A',self.n])

