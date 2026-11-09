"""Adversarial and positive checks of both implementations; no assert statements."""
import unittest
import kernel as k
import check_debruijn as d

class Both:
    def __init__(self):self.a=k.Kernel();self.b=d.Checker()
    def step(self,r,refs=(),args=()):
        ia=self.a.add(r,refs,args);h,c=self.b.step(r,refs,args)
        if d.normal(d.convert(self.a.proofs[ia].conclusion))!=c:raise RuntimeError('implementations disagree')
        return ia
    def reject(self,r,refs=(),args=()):
        for fn in (lambda:self.a.add(r,refs,args),lambda:self.b.step(r,refs,args)):
            try:fn()
            except (k.CheckError,d.Invalid):continue
            raise RuntimeError('invalid inference accepted')

class KernelTests(unittest.TestCase):
    def test_bad_modus_ponens(self):
        e=Both();p=k.V('p',k.O);q=k.V('q',k.O)
        a=e.step('assume',args=(k.Imp(p,q),));b=e.step('assume',args=(q,));e.reject('imp_e',(a,b))
    def test_false_conversion(self):
        e=Both();p=k.V('p',k.O);a=e.step('em',args=(p,));e.reject('conv',(a,),(k.Bot,))
    def test_no_unproved_axiom_rule(self):Both().reject('axiom',args=(k.Bot,))
    def test_no_circular_reference(self):Both().reject('imp_e',(0,0))
    def test_illegal_generalization(self):
        e=Both();x=k.V('x','X');p=k.V('P',k.Arr('X',k.O));a=e.step('assume',args=(k.App(p,x),));e.reject('all_i',(a,),(x,))
    def test_escaping_existential_witness(self):
        e=Both();x=k.V('x','X');v=k.V('v','X');p=k.V('P',k.Arr('X',k.O))
        a=e.step('assume',args=(k.Ex(x,k.App(p,x)),));b=e.step('assume',args=(k.App(p,v),));e.reject('ex_e',(a,b),(v,))
    def test_nonfresh_existential_witness(self):
        e=Both();x=k.V('x','X');v=k.V('v','X');p=k.V('P',k.Arr('X',k.Arr('X',k.O)))
        f=k.Ex(x,k.Not(k.App(k.App(p,x),v)))
        a=e.step('assume',args=(f,));b=e.step('assume',args=(k.Bot,));e.reject('ex_e',(a,b),(v,))
    def test_invalid_existential_witness(self):
        e=Both();x=k.V('x','X');v=k.V('v','X');p=k.V('P',k.Arr('X',k.O));q=k.V('Q',k.Arr('X',k.O))
        a=e.step('assume',args=(k.App(q,v),));e.reject('ex_i',(a,),(k.Ex(x,k.App(p,x)),v))
    def test_type_mismatch(self):
        e=Both();x=k.V('x','X');p=k.V('P',k.Arr('X',k.O));a=e.step('assume',args=(k.All(x,k.App(p,x)),));e.reject('all_e',(a,),(k.V('y','Y'),))
    def test_proposition_type_cannot_change(self):
        e=Both();p=k.V('p',k.O);a=e.step('em',args=(p,));e.reject('type_inst',(a,),((('o','X'),),))
    def test_type_instantiation_avoids_capture(self):
        e=Both();x=k.V('x','X');y=k.V('x','Y');p=k.V('P',k.Arr('X',k.Arr('Y',k.O)))
        f=k.All(x,k.App(k.App(p,x),y));a=e.step('assume',args=(f,))
        b=e.step('type_inst',(a,),((('Y','X'),),))
        out=e.a.proofs[b].conclusion
        if k.V('x','X') not in k.fv(out):raise RuntimeError('free variable captured')
    def test_identity_and_beta(self):
        e=Both();p=k.V('p',k.O);q=k.V('q',k.O);a=e.step('assume',args=(p,));b=e.step('imp_i',(a,),(p,))
        if e.a.proofs[b].assumptions:raise RuntimeError('identity has assumptions')
        e.step('conv',(b,),(k.App(k.Lam(q,k.Imp(q,q)),p),))
    def test_keeps_undischarged_hypotheses(self):
        e=Both();p=k.V('p',k.O);q=k.V('q',k.O);a=e.step('assume',args=(q,));b=e.step('imp_i',(a,),(p,))
        if len(e.a.proofs[b].assumptions)!=1:raise RuntimeError('lost assumption')
    def test_valid_existential_elimination(self):
        e=Both();x=k.V('x','X');v=k.V('v','X');p=k.V('P',k.Arr('X',k.O));q=k.V('q',k.O)
        a=e.step('assume',args=(k.Ex(x,k.App(p,x)),));b=e.step('assume',args=(q,));e.step('ex_e',(a,b),(v,))

if __name__=='__main__':unittest.main(verbosity=2)
