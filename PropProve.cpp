#include <algorithm>
#include <iostream>
#include <list>
#include <memory>
#include <set>
#include <string>

using namespace std;;

class Show {
  public:
    virtual string show() = 0;
};

ostream& operator<<(std::ostream& os, Show& s) {
  os << s.show(); return os;
}

template <class T> T operator+(T t1, T t2) {
  T t(t1);
  t.insert(t2.begin(), t2.end());
  return t;
}

template <class T> string show_strings(T ss) {
  for_each(ss.begin(), prev(ss.end()), [] (string &s) { s += ", "; });
  return accumulate(ss.begin(), ss.end(), string(""));
}


// -----------------------------------------------------------------------------
// Terms

class Term : public Show
{
};

typedef shared_ptr<Term> TermP;
typedef set<TermP> Terms;

string show_terms(Terms ts) {
  list<string> ss;
  for (const auto t : ts) ss.push_back(t->show());
  return show_strings(ss);
}

class Variable : public Term
{
  private:
    string name;

  public:
    Variable(string n) : name(n) {}
    virtual string show() { return name; }
};

class And : public Term
{
  private:
    TermP left, right;

  public:
    And(TermP l, TermP r) : left(l), right(r) {}
    virtual string show() { return left->show() + " /\\ " + right->show(); }
};

/*
class Or : public Term
{
  Or(Term, Term);
};
*/

// -----------------------------------------------------------------------------
// Proofs

class Proof : public Show
{
  public:
    virtual Terms premises() = 0;
    virtual TermP conclusion() = 0;

    string show() {
      return show_terms(premises()) + " |- " + conclusion()->show();
    }
};

typedef shared_ptr<Proof> ProofP;

enum LR {Left, Right};

class Conj : public Proof
{
  private:
    ProofP left, right;

  public:
    Conj(ProofP l, ProofP r) : left(l), right(r) {}

    ProofP disch(LR);

    virtual Terms premises() {
      return left->premises() + right->premises();
    }
    virtual TermP conclusion() {
      return TermP(new And(left->conclusion(), right->conclusion()));
    }
};

/*
class Disj : public Proof
{
  Disj(LR, Proof p, Term&);

  Proof disch(Proof, Proof);
};
*/

class Assume : public Proof
{
  private:
    TermP term;
  public:
    Assume (TermP t) : term(t) {}

    virtual Terms premises() { return {term}; }
    virtual TermP conclusion() { return term; }
};



int main()
{
  ProofP a(new Assume(TermP(new Variable("a"))));
  ProofP b(new Assume(TermP(new Variable("b"))));
  ProofP conj(new Conj(a, b));
  cout << (*conj) << endl;
  return 0;
}
