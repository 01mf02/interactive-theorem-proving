#include <algorithm>
#include <iostream>
#include <list>
#include <memory>
#include <set>
#include <string>

using namespace std;;

class Show {
  public:
    virtual string show() const = 0;
};

ostream& operator<<(std::ostream& os, const Show& s) {
  os << s.show(); return os;
}

template <class T> T id(T x) {
  return x;
}

template <class T> class Maybe {
  private:
    T &x;
    bool just;

  public:
    Maybe() : x(nullptr), just(false) {}
    Maybe(T x) : x(x), just(true) {}

    template <class R> R maybe(R r, R (*f)(T)) {
      if (just) return r;
      else return f(x);
    }
};

// Concatenate containers supporting `insert`.
template <class T> T operator+(const T t1, const T t2) {
  T t(t1);
  t.insert(t2.begin(), t2.end());
  return t;
}

// Return comma-separated string of a container of strings.
template <class T> string show_strings(T ss) {
  for_each(ss.begin(), prev(ss.end()), [] (string &s) { s += ", "; });
  return accumulate(ss.begin(), ss.end(), string(""));
}


// -----------------------------------------------------------------------------
// Terms

class Term : public Show {
};

typedef shared_ptr<const Term> TermP;
typedef set<TermP> Terms;

string show_terms(Terms ts) {
  list<string> ss;
  for (const auto t : ts) ss.push_back(t->show());
  return show_strings(ss);
}

class Variable : public Term {
  private:
    string name;

  public:
    Variable(string n) : name(n) {}
    virtual string show() const { return name; }
};

TermP mk_variable(string n) { return TermP(new Variable(n)); }

enum Connective {And, Or, Implies};

string show_connective(Connective c) {
  string s;
  if      (c == And) s = "/\\";
  else if (c == Or ) s = "\\/";
  else               s = "->";

  return " " + s + " ";
}

class PairTerm : public Term {
  private:
    TermP left;
    Connective conn;
    TermP right;

  public:
    PairTerm(TermP l, Connective c, TermP r) : left(l), conn(c), right(r) {}
    virtual string show() const {
      return left->show() + show_connective(conn) + right->show();
    }
};

TermP mk_and(TermP l, TermP r) { return TermP(new PairTerm(l, And, r)); }
TermP mk_or (TermP l, TermP r) { return TermP(new PairTerm(l,  Or, r)); }

class Not : public Term {
  private:
    TermP term;

  public:
    Not(TermP t) : term(t) {}
    virtual string show() const { return "~" + term->show(); }
};

TermP mk_not (TermP t) { return TermP(new Not(t)); }


// -----------------------------------------------------------------------------
// Proofs

class Proof : public Show {
  public:
    virtual Terms premises() const = 0;
    virtual TermP conclusion() const = 0;

    string show() const {
      return show_terms(premises()) + " |- " + conclusion()->show();
    }
};

typedef shared_ptr<Proof> ProofP;

enum LR {Left, Right};

template <class T> T left_right(LR lr, T l, T r) {
  if (lr == Left) return l; else return r;
}

class Conj : public Proof
{
  private:
    ProofP left, right;

  public:
    Conj(ProofP l, ProofP r) : left(l), right(r) {}

    ProofP disch(LR s) const { return left_right(s, left, right); }

    virtual Terms premises() const { return left->premises() + right->premises(); }
    virtual TermP conclusion() const {
      return mk_and(left->conclusion(), right->conclusion());
    }
};

ProofP mk_conj(ProofP l, ProofP r) { return ProofP(new Conj(l, r)); }

class Disj : public Proof {
  private:
    LR proof_side;
    ProofP proof;
    TermP term;

  public:
    Disj(ProofP p, TermP t) : proof_side(Left ), proof(p), term(t) {}
    Disj(TermP t, ProofP p) : proof_side(Right), proof(p), term(t) {}

    ProofP disch(ProofP, ProofP);

    virtual Terms premises() const { return proof->premises(); }
    virtual TermP conclusion() const { return left_right(proof_side,
      mk_or(proof->conclusion(), term),
      mk_or(term, proof->conclusion()));
    }
};

ProofP mk_disj(ProofP l, TermP r) { return ProofP(new Disj(l, r)); }
ProofP mk_disj(TermP l, ProofP r) { return ProofP(new Disj(l, r)); }

class Assume : public Proof {
  private:
    TermP term;
  public:
    Assume (TermP t) : term(t) {}

    virtual Terms premises() const { return {term}; }
    virtual TermP conclusion() const { return term; }
};

ProofP mk_assume(TermP t) { return ProofP(new Assume(t)); }


// -----------------------------------------------------------------------------
// Main

int main() {
  ProofP a = mk_assume(mk_not(mk_variable("a")));
  ProofP b = mk_assume(mk_variable("b"));
  ProofP thm = mk_disj(mk_conj(a, b), mk_variable("x"));
  cout << (*thm) << endl;

  return 0;
}
