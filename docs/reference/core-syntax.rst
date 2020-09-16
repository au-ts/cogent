************************************************************************
                              Core Syntax
************************************************************************

.. todo:: (jashankj, 2020-02-13): document the core syntax

|cogent|'s 'core' language is not directly exposed to programmers.
Nonetheless, it's extremely useful to know how
|cogent| turns its more expressive surface syntax
into the core language used for proofs and code generation.


.. math::

   \begin{array}{llclr}
     \text{expressions}
     &  e  &  ::=  &  x \;|\; l & \\
     &     &   |   &  e_1 \wr e_2       & \text{(primops)} \\
     &     &   |   &  e_1 e_2 \quad|\quad f\, \textbf{[} \tau_i \textbf{]}
                                        & \text{(applications)} \\
     &     &   |   &  \textbf{let}\; x = e_1 \;\textbf{in}\; e_2 & \\
     &     &   |   &  \textbf{if}\; e_1 \;\textbf{then}\; e_2 \;\textbf{else}\; e_3 & \\
     &     &   |   &  e :: \tau         & \text{(type signatures)} \\
     &     &   |   &  \ldots            & \\
     \text{types}
     & \tau,
      \rho &  ::=  & a                  & \text{(type variables)} \\
     &     &   |   & \alpha             & \text{(unknowns)} \\
     &     &   |   & \tau_1 \to \tau_2  & \text{(functions)} \\
     &     &   |   & T \quad|\quad \cdots   & \\
     \text{prim. types}
     &  T  &  ::=  & \texttt{U8}
               \;|\; \texttt{U16}
               \;|\; \texttt{U32}
               \;|\; \texttt{U64}       & \text{(integral types)} \\
     &     &   |   & \texttt{Bool} & \\
     \text{operators}
     & \wr &  ::=  & +
               \;|\; \le
               \;|\; \ne
               \;|\; \wedge
               \;|\; \cdots & \\
     \text{literals}
     &  L  &  ::=  & \texttt{True}
               \;|\; \texttt{False}
               \;|\; \mathbf{N} & \\
     \text{constraints}
     &  C  &  ::=  & C_1 \wedge C_2     & \text{(conjunction)} \\
     &     &   |   & L \in \tau         & \text{(integer bounds)} \\
     &     &   |   & \tau_1\eqsim\tau_2 & \text{(equality)} \\
     &     &   |   & \tau_1\sqsubseteq\tau_2
                                        & \text{(subtyping)} \\
     &     &   |   & \tau\,\textbf{Share}
               \;|\; \tau\,\textbf{Drop} &\text{(contract/weaken)} \\
     &     &   |   & \top \;|\; \bot    & \\
     \text{contexts}
     & \Gamma &  ::=  & \overline{x : \tau} & \\
     \text{alg. contexts}
     &   G    &  ::=  & \overline{x :_{\langle n \rangle} \tau} & \\
     \text{axiom sets}
     &   A    &  ::=  & \overline{a_i \,\textbf{Drop}},
                        \overline{b_j \,\textbf{Share}} & \\
     \text{polytypes}
     &  \pi   &  ::=  & \forall\overset{\rightharpoonup}{a}.  C \Rightarrow \tau & \\
     \text{type vars}     &  a, b, c  & & & \\
     \text{unknowns}      &  \alpha, \beta, \gamma  & & & \\
     \text{variables}     &  x, y, z  & & & \\
     \text{usage counts}  &  m, n  & & & \\
   \end{array}

