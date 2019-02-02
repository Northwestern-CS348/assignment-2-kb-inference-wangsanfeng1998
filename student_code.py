import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        
        # for is shorthand for fact_or_rule
        if isinstance(fact_or_rule, Rule):
            if fact_or_rule not in self.rules: #for is not a fact in the kb
                return None
            else:
                if fact_or_rule.asserted == False and len(fact_or_rule.supported_by) == 0: #this section removes rules that are no longer asserted or supported - ONLY the result of a recursive call
                    fact_or_rule = self._get_rule(fact_or_rule)
                    for f in fact_or_rule.supports_facts: #iterate through the facts that for supports, and remove its support
                        f = self._get_fact(f)
                        for fpair in f.supported_by:
                            if fact_or_rule in fpair:
                                f.supported_by.remove(fpair)
                                fpair[1].supports_facts.remove(f)
                        if (len(f.supported_by) == 0) and (f.asserted != True): #if the fact is not asserted AND no longer has other facts to support it, then it can also be removed (implemented as a recursive call of retract)
                            self.kb_retract(f)

                    for r in fact_or_rule.supports_rules: #iterate through the rules that for supports, and remove its support
                        r = self._get_rule(r)
                        for rpair in r.supported_by:
                            if fact_or_rule in rpair:
                                r.supported_by.remove(rpair)
                                rpair[1].supports_rules.remove(r)
                        if (len(r.supported_by) == 0) and (r.asserted != True): #if the rule is not asserted AND no longer has other facts to support it, then it can also be removed (implemented as a recursive call of retract)
                            self.kb_retract(r)
                    self.rules.remove(fact_or_rule)
                else:
                    return None #asserted rules or rules that still have support cannot be changed

        else: #for is a Fact
            if fact_or_rule not in self.facts: #for is not a fact in the kb
                return None
            else:
                fact_or_rule = self._get_fact(fact_or_rule)
                if fact_or_rule.asserted: #make sure that the fact is changed to be unasserted
                    fact_or_rule.asserted = False
                if len(fact_or_rule.supported_by) == 0: #for is not asserted anymore, and has no support, should be removed
                    for f in fact_or_rule.supports_facts:
                        f = self._get_fact(f)
                        for fpair in f.supported_by:
                            if fact_or_rule in fpair:
                                f.supported_by.remove(fpair)
                                fpair[1].supports_facts.remove(f)
                        if (len(f.supported_by) == 0) and (f.asserted != True): #if the fact is not asserted AND no longer has other facts to support it, then it can also be removed (implemented as a recursive call of retract)
                           self.kb_retract(f)

                    for r in fact_or_rule.supports_rules:
                        r = self._get_rule(r)
                        for rpair in r.supported_by:
                            if fact_or_rule in rpair:
                                r.supported_by.remove(rpair)
                                rpair[1].supports_rules.remove(r)
                        if (len(r.supported_by) == 0) and (r.asserted != True): #if the rule is not asserted AND no longer has other facts to support it, then it can also be removed (implemented as a recursive call of retract)
                            self.kb_retract(r)
                    self.facts.remove(fact_or_rule)
                else: #for is not asserted anymore, but still has support, should not be removed
                    return None
                    

        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        #get the first rule on the left hand side
        first_rule = rule.lhs[0]

        binding = match(first_rule,fact.statement)
        #rule.rhs is always length 1
        if binding:
            observation = instantiate(rule.rhs, binding)
            if len(rule.lhs) > 1:
                #observation must be a rule 
                rest_of_lhs = []
                for r in rule.lhs[1:]:
                    rest_of_lhs.append(instantiate(r, binding))
                new_rule = Rule([rest_of_lhs, observation], [(fact, rule)])
                #if the conditions on the left are met, then the observation is true (rule.rhs -> (first rule, fact))
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_assert(new_rule)
            else: #observation must be a fact
                new_fact = Fact(observation, [(fact, rule)])
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                kb.kb_assert(new_fact)
                #is an inferred fact
            return None
        else:
            return None
