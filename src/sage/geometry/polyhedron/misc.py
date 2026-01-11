r"""
Miscellaneous helper functions
"""
# **********************************************************************
#       Copyright (C) 2008 Marshall Hampton <hamptonio@gmail.com>
#       Copyright (C) 2011 Volker Braun <vbraun.name@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  https://www.gnu.org/licenses/
# **********************************************************************

from sage.misc.flatten import flatten
from sage.structure.element import parent
from sage.categories.fields import Fields
from sage.categories.rings import Rings


def _to_space_separated_string(l, base_ring=None):
    """
    Convert a container to a space-separated string.

    INPUT:

    - ``l`` -- anything iterable

    - ``base_ring`` -- ring (default: ``None``); convert this ring, if given

    OUTPUT: string

    EXAMPLES::

        sage: import sage.geometry.polyhedron.misc as P
        sage: P._to_space_separated_string([2,3])
        '2 3'
        sage: P._to_space_separated_string([2, 1/5], RDF)                               # needs sage.rings.real_double
        '2.0 0.2'
    """
    if base_ring:
        return ' '.join(repr(base_ring(x)) for x in l)
    return ' '.join(repr(x) for x in l)


def _set_to_None_if_empty(x):
    """
    Helper function to clean up arguments.

    This returns None if x is None or x is an empty container.

    EXAMPLES::

        sage: import sage.geometry.polyhedron.misc as P
        sage: None == P._set_to_None_if_empty([])
        True
        sage: P._set_to_None_if_empty([1])
        [1]
    """
    if x is None:
        return x
    x = list(x)
    if not x:
        return None
    return x


def _make_listlist(x):
    """
    Helper function to clean up arguments.

    INPUT:

    - ``x`` -- ``None`` or an iterable of iterables

    OUTPUT: list of lists

    EXAMPLES::

        sage: import sage.geometry.polyhedron.misc as P
        sage: [] == P._make_listlist(tuple())
        True
        sage: [] == P._make_listlist(None)
        True
        sage: P._make_listlist([(1,2),[3,4]])
        [[1, 2], [3, 4]]
    """
    if x is None:
        return []
    return [list(y) for y in x]


def _common_length_of(l1, l2=None, l3=None):
    """
    The arguments are containers or ``None``. The function applies
    ``len()`` to each element, and returns the common length. If the
    length differs, :exc:`ValueError` is raised. Used to check arguments.

    OUTPUT:

    A tuple (number of entries, common length of the entries)

    EXAMPLES::

        sage: import sage.geometry.polyhedron.misc as P
        sage: P._common_length_of([[1,2,3],[1,3,34]])
        (2, 3)
    """
    args = []
    if l1 is not None:
        args.append(l1)
    if l2 is not None:
        args.append(l2)
    if l3 is not None:
        args.append(l3)

    length = None
    num = 0
    for l in args:
        for i in l:
            num += 1
            length_i = len(i)
            if length is not None and length_i != length:
                raise ValueError("Argument lengths differ!")
            length = length_i

    return num, length

def _find_base_ring(actual_base_ring, vertices=None, rays=None, lines=None, ieqs=None, eqns=None, got_Vrep=False, got_Hrep=False):

    r"""
    Determine an appropriate base ring for a polyhedron given its data.

    This function inspects the coordinates of the vertices, rays, lines,
    inequalities, and equations describing a polyhedron and deduces the
    smallest suitable base ring. If ``actual_base_ring`` is provided, the
    function may also check whether the given data needs to be converted
    to that ring.

    INPUT:

    - ``actual_base_ring`` -- a ring or ``None``;
      initial base ring guess.

    - ``vertices`` -- list (default: ``None``);
      list of vertices (each iterable of coordinates).

    - ``rays`` -- list (default: ``None``);
      list of rays.

    - ``lines`` -- list (default: ``None``);
      list of lines.

    - ``ieqs`` -- list (default: ``None``);
      list of inequalities.

    - ``eqns`` -- list (default: ``None``);
      list of equations.

    - ``got_Vrep`` -- boolean (default: ``False``);
      whether a V-representation (vertices/rays/lines) was given.

    - ``got_Hrep`` -- boolean (default: ``False``);
      whether an H-representation (inequalities/equations) was given.

    OUTPUT:

    A tuple ``(base_ring, convert)`` where:

    - ``base_ring`` -- the determined base ring for the polyhedron.
    - ``convert`` -- boolean, ``True`` if the input data needs to be converted
      to the returned ``base_ring``.

    EXAMPLES::

        sage: find_base_ring(None, vertices=[[1, 0], [0, 1]], got_Vrep=True)
        (Integer Ring, False)

        sage: find_base_ring(None, vertices=[[1/2, 0], [0, 1]], got_Vrep=True)
        (Rational Field, True)

        sage: find_base_ring(RR, vertices=[[1.0, 0.0]], got_Vrep=True)
        (Real Field with 53 bits of precision, False)
    """

    values = flatten((vertices if vertices else []) + (rays if rays else []) + (lines if lines else []) + (ieqs if ieqs else []) + (eqns if eqns else []))
    if actual_base_ring is not None:
        convert = any(parent(x) is not actual_base_ring for x in values)
    elif not values:
        actual_base_ring = ZZ
        convert = False
    else:
        P = parent(values[0])
        if any(parent(x) is not P for x in values):
            from sage.structure.sequence import Sequence
            P = Sequence(values).universe()
            convert = True
        else:
            convert = False

        from sage.structure.coerce import py_scalar_parent
        if isinstance(P, type):
            actual_base_ring = py_scalar_parent(P)
            convert = convert or P is not actual_base_ring
        else:
            actual_base_ring = P

        if actual_base_ring not in Fields():
            got_compact_Vrep = got_Vrep and not rays and not lines
            got_cone_Vrep = got_Vrep and all(x == 0
                                             for v in vertices for x in v)
            if not got_compact_Vrep and not got_cone_Vrep:
                actual_base_ring = actual_base_ring.fraction_field()
                convert = True

        if actual_base_ring not in Rings():
            raise ValueError('invalid base ring')

        try:
            from sage.symbolic.ring import SR
        except ImportError:
            SR = None
        if actual_base_ring is not SR and not actual_base_ring.is_exact():
            try:
                from sage.rings.real_double import RDF
            except ImportError:
                RDF = None
            try:
                from sage.rings.real_mpfr import RR
            except ImportError:
                RR = None
            # TODO: remove this hack?
            if actual_base_ring is RR:
                actual_base_ring = RDF
                convert = True
            elif actual_base_ring is not RDF:
                raise ValueError("the only allowed inexact ring is 'RDF' with backend 'cdd'")
    return actual_base_ring, convert
