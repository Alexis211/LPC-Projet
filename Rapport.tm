<TeXmacs|1.0.7.19>

<style|generic>

<\body>
  <doc-data|<doc-title|Langages de Programmation et
  Compilation>|<doc-author|>|<doc-author|<author-data|<author-name|Alex
  AUVOLAT, Louis GARRIGUE>>>>

  Les indications et contraintes données par le sujet ont été suivies et
  devraient être facilement compréhensibles. Voici quelques précisions sur
  certaines décisions prises à l'élaboration des lexer/parser.

  <\itemize>
    <item>La règle <verbatim|strval> du lexer permet de traîter les séquences
    d'échappement dans les chaînes de caractères.

    <item>Le <em|lexer hack>, permettant de remédier aux ambiguïtés de la
    grammaire, est défini : lorsque le parser rencontre une occurence
    <verbatim|CLASS n = IDENT>, il ajoute l'identificateur <math|n> à la
    table d'association contenant les types, partagée par le parser et le
    lexer dans l'AST. Les occurences suivantes de <math|n> seront donc prises
    comme des identificateurs de type.

    <item>L'associativité à droite des opérateurs unaires <verbatim|! ++ -- &
    * + -> est traduite par les dérivations dans la grammaire définies par
    <verbatim|lunop>.

    <item>La localisation d'erreur de compilation est traitée pour tous les
    non-terminaux dont la dérivation contient au moins un non-terminal.

    <item>Des structures intermédiaires <verbatim|typed_q?vars?> sont
    définies pour traduire les occurences <verbatim|\<less\>type\<gtr\>
    \<less\>var\<gtr\>, \<less\>type\<gtr\> \<less\>var\<gtr\>+,
    \<less\>type\<gtr\> \<less\>qvar\<gtr\>>. \ La fonction
    <verbatim|reverse> définie au début du parser permet d'inverser le sens
    de <verbatim|*> et <verbatim|&> (et de préciser le type pointeur ou
    référence) si on a par exemple une expression de la forme <verbatim|int
    &*p>, pour que la compilation traite la sémantique souhaitée lors du
    codage.

    <item>Les <verbatim|qvar> se traduisent en une paire : le premier membre
    indique l'identificateur (peut être un pointeur ou une référence vers un
    identificateur) et le second indique s'il s'agit d'une classe, et précise
    la classe le cas échéant.

    <item>Le non-terminal <verbatim|statement> fait appel à deux
    non-terminaux pour différents statements :

    <\itemize>
      <item>Ceux ne contenant pas d'instruction <verbatim|if> :
      <verbatim|no_if_statement> ;\ 

      <item>Ceux ne contenant pas d'instruction <verbatim|if>,
      <verbatim|for>, ou <verbatim|while> : <verbatim|common_statement>
    </itemize>

    La construction <verbatim|no_if_statement> permet de traduire le fait que
    lorsqu'un <verbatim|else> peut se rapporter à plusieurs <verbatim|if>, il
    se rapporte au <verbatim|if> le plus proche.

    <item>Les expressions sont décomposées elles aussi en plusieurs
    sous-structures pour une exploitation plus pratique. Dans
    <verbatim|expression>, les dérivations où apparaît zéro ou une fois une
    expression sont traitées de façon séparée : avec <verbatim|runop>, puis
    <verbatim|lunop>, puis <verbatim|primary>. \ Certaines érivations
    inutiles de la grammaire sont ainsi évitées : par exemple, dans
    <verbatim|expr-\<gtr\>ident> ou <verbatim|expr.ident>, <math|expr> ne
    peut pas se dériver en une assignation <verbatim|\<less\>e1\<gtr\> =
    \<less\>e2\<gtr\>> (à moins qu'elle soit entre parenthèses), mais qu'en
    une expression "primaire" <verbatim|primary> (identificateur, this, NULL,
    constante, booléen ou expression entre parenthèse), ce qui résoud un
    certain nombre de conflits de la grammaire.

    <item><verbatim|cls_proto> évite que la grammaire crée une dérivation
    produisant l'appel d'une classe lors de la définition d'une autre. En
    effet, lors d'une telle définition, il faut rappeler que l'on ne doit pas
    avoir accès à d'autres classes externes.
  </itemize>

  Tous les tests fournis ont été vérifiés corrects.

  \;

  \;

  \;
</body>

<\initial>
  <\collection>
    <associate|language|french>
  </collection>
</initial>