#include <algorithm>
#include <iostream>
#include <list>
#include <memory>
#include <set>
#include <string>
#include <utility>

using namespace std;;

class Show {
  public:
    virtual string show() const = 0;
};

ostream& operator<<(std::ostream& os, const Show& s) {
  os << s.show(); return os;
}

class Error: public std::exception {
  private:
    string message;

  public:
    Error(const string& m) : message(m) {}
    virtual const char* what() const throw() {
        return message.c_str();
    }
};

void fail(string s) { throw Error(s); }

template <class T> T id(T x) {
  return x;
}

template <class T> class Maybe {
  private:
    shared_ptr<T> p;

  public:
    Maybe() {}
    Maybe(T x) : p(new T(x)) {}

    template <class R> R maybe(R r, R (*f)(T)) {
      if (p) return f(*p);
      else return r;
    }
};

template <class T> Maybe<T> maybe_from_boolean(T x) {
  if (x) return Maybe<T>(x); else return Maybe<T>();
}

template <class T, class U> Maybe<shared_ptr<T> > maybe_cast(U p) {
  return maybe_from_boolean(dynamic_pointer_cast<T>(p));
}

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

class Terms : public set<TermP>, public Show {
  using set::set;

  public:
    string show() const {
      list<string> ss;
      for (const auto t : (*this)) ss.push_back(t->show());
      return show_strings(ss);
    }
};


class Variable : public Term {
  private:
    string name;

  public:
    Variable(string n) : name(n) {}
    virtual string show() const { return name; }
};

TermP mk_variable(string n) { return TermP(new Variable(n)); }




class PairTerm : public Term, public pair<TermP, TermP> {
  protected:
    enum Connective {AndConn, OrConn, ImpliesConn};

  private:
    Connective conn;

    string show_connective(Connective c) const {
      if      (c == AndConn) return "/\\";
      else if (c == OrConn ) return "\\/";
      else                   return "->";
    }

  protected:
    PairTerm(TermP l, Connective c, TermP r) : pair(l, r), conn(c) {}

  public:
    virtual string show() const {
      return first->show() + " " + show_connective(conn) + " " + second->show();
    }
};

class And : public PairTerm {
  public:
    And(TermP l, TermP r) : PairTerm(l, AndConn, r) {}
};

class Or : public PairTerm {
  public:
    Or(TermP l, TermP r) : PairTerm(l, OrConn, r) {}
};

class Implies : public PairTerm {
  public:
    Implies(TermP l, TermP r) : PairTerm(l, ImpliesConn, r) {}
};

typedef shared_ptr<const     And>     AndP;
typedef shared_ptr<const      Or>      OrP;
typedef shared_ptr<const Implies> ImpliesP;

TermP mk_and    (TermP l, TermP r) { return TermP(new     And(l, r)); }
TermP mk_or     (TermP l, TermP r) { return TermP(new      Or(l, r)); }
TermP mk_implies(TermP l, TermP r) { return TermP(new Implies(l, r)); }

Maybe<    AndP> dt_and    (TermP t) { return maybe_cast<const     And>(t); }
Maybe<     OrP> dt_or     (TermP t) { return maybe_cast<const      Or>(t); }
Maybe<ImpliesP> dt_implies(TermP t) { return maybe_cast<const Implies>(t); }


class Not : public Term {
  private:
    TermP term;

  public:
    Not(TermP t) : term(t) {}
    virtual string show() const { return "~" + term->show(); }
};

typedef shared_ptr<const Not> NotP;

TermP mk_not (TermP t) { return TermP(new Not(t)); }

Maybe<NotP> dt_not(TermP t) { return maybe_cast<const Not>(t); }



// -----------------------------------------------------------------------------
// Proofs

class Proof : public Show {
  public:
    virtual Terms premises() const = 0;
    virtual TermP conclusion() const = 0;

    string show() const {
      return premises().show() + " |- " + conclusion()->show();
    }
};

typedef shared_ptr<Proof> ProofP;

enum LR {Left, Right};

template <class T> T left_right(LR lr, T l, T r) {
  if (lr == Left) return l; else return r;
}

class Conj : public Proof {
  private:
    ProofP left, right;

  public:
    Conj(ProofP l, ProofP r) : left(l), right(r) {}

    ProofP disch(LR s) const { return left_right(s, left, right); }

    virtual Terms premises() const {
      return left->premises() + right->premises();
    }
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

    ProofP disch(ProofP l, ProofP r) {
      return nullptr;
    }

    virtual Terms premises() const { return proof->premises(); }
    virtual TermP conclusion() const { return left_right(proof_side,
      mk_or(proof->conclusion(), term),
      mk_or(term, proof->conclusion()));
    }
};

ProofP mk_disj(ProofP l, TermP r) { return ProofP(new Disj(l, r)); }
ProofP mk_disj(TermP l, ProofP r) { return ProofP(new Disj(l, r)); }


class Impl : public Proof {
  private:
    TermP term;
    ProofP proof;

  public:
    Impl(TermP t, ProofP p) : term(t), proof(p) {}

    ProofP disch(ProofP p) {
      if (p->conclusion() == term)
        return nullptr; //(p->premises() + premises(), p->conclusion());
    }

    virtual Terms premises() const {
      Terms prems(proof->premises());
      if (prems.erase(term) == 1) return prems;
      else fail("Implication premise not in proof premises.");
    }

    virtual TermP conclusion() const {
      return mk_implies(term, proof->conclusion());
    }
};

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

  Terms vars({mk_variable("a"), mk_variable("b")});
  cout << vars << endl;

  return 0;
}
