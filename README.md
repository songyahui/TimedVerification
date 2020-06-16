# Automate Verification of Timed Temporal Properties via User-Defined Predicates

It is prevalent to use automata-theoretic approaches for specification and verification of timed systems, which have either sacrificed compositionality in favor of achieving automation or vice-versa. To exploit the best of both worlds, we present a new solution to ensure temporal properties via a Hoare-style verifier and a term rewriting system (T.r.s) on Timed Dependent Effects. The first contribution is a novel effects logic extending the timed language with dependent values, which is beyond the expressive power of finite-state machine. As a second contribution, by avoiding the complex translation into automata, our purely algebraic T.r.s efficiently checks the temporal properties described by Timed Temporal Logic. Besides, our approach uses user-definable predicates to allow programmers to describe a wide range of temporal properties. We prototype this logic on top of the HIP/SLEEK system and show the feasibility of our method using a number of case studies.

## Online demo

The easiest way to try the code is to use the [Web UI](http://loris-5.d2.comp.nus.edu.sg/TimedEffect/index.html?ex=send_valid&type=c&options=sess) written
by [Yahui Song](https://www.comp.nus.edu.sg/~yahuis/).

### To Compile:

```
git clone https://github.com/songyahui/TimedVerification.git
cd TimedVerification
chmod 755 clean 
chmod 755 compile 
./compile
```

### Dependencies:

```
opam switch create 4.07.1
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install z3


# TimedVerification

1. first to propose a Hoare style timed verifciation
2. verification locally
3. allow more expressive specifications
