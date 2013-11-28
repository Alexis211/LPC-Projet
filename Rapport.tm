<TeXmacs|1.0.7.19>

<style|generic>

<\body>
  <doc-data|<doc-title|Langages de Programmation et
  Compilation>|<doc-author|>|<doc-author|<author-data|<author-name|Alex
  AUVOLAT, Louis GARRIGUE>>>>

  Les indications et contraintes donn�es par le sujet ont �t� suivies et
  devraient �tre facilement compr�hensibles. Voici quelques pr�cisions sur
  certaines d�cisions prises � l'�laboration des lexer/parser.

  <\itemize>
    <item>La r�gle <verbatim|strval> du lexer permet de tra�ter les s�quences
    d'�chappement dans les cha�nes de caract�res.

    <item>Le <em|lexer hack>, permettant de rem�dier aux ambigu�t�s de la
    grammaire, est d�fini : lorsque le parser rencontre une occurence
    <verbatim|CLASS n = IDENT>, il ajoute l'identificateur <math|n> � la
    table d'association contenant les types, partag�e par le parser et le
    lexer dans l'AST. Les occurences suivantes de <math|n> seront donc prises
    comme des identificateurs de type.

    <item>L'associativit� � droite des op�rateurs unaires <verbatim|! ++ -- &
    * + -> est traduite par les d�rivations dans la grammaire d�finies par
    <verbatim|lunop>.

    <item>La localisation d'erreur de compilation est trait�e pour tous les
    non-terminaux dont la d�rivation contient au moins un non-terminal.

    <item>Des structures interm�diaires <verbatim|typed_q?vars?> sont
    d�finies pour traduire les occurences <verbatim|\<less\>type\<gtr\>
    \<less\>var\<gtr\>, \<less\>type\<gtr\> \<less\>var\<gtr\>+,
    \<less\>type\<gtr\> \<less\>qvar\<gtr\>>. \ La fonction
    <verbatim|reverse> d�finie au d�but du parser permet d'inverser le sens
    de <verbatim|*> et <verbatim|&> (et de pr�ciser le type pointeur ou
    r�f�rence) si on a par exemple une expression de la forme <verbatim|int
    &*p>, pour que la compilation traite la s�mantique souhait�e lors du
    codage.

    <item>Les <verbatim|qvar> se traduisent en une paire : le premier membre
    indique l'identificateur (peut �tre un pointeur ou une r�f�rence vers un
    identificateur) et le second indique s'il s'agit d'une classe, et pr�cise
    la classe le cas �ch�ant.

    <item>Le non-terminal <verbatim|statement> fait appel � deux
    non-terminaux pour diff�rents statements :

    <\itemize>
      <item>Ceux ne contenant pas d'instruction <verbatim|if> :
      <verbatim|no_if_statement> ;\ 

      <item>Ceux ne contenant pas d'instruction <verbatim|if>,
      <verbatim|for>, ou <verbatim|while> : <verbatim|common_statement>
    </itemize>

    La construction <verbatim|no_if_statement> permet de traduire le fait que
    lorsqu'un <verbatim|else> peut se rapporter � plusieurs <verbatim|if>, il
    se rapporte au <verbatim|if> le plus proche.

    <item>Les expressions sont d�compos�es elles aussi en plusieurs
    sous-structures pour une exploitation plus pratique. Dans
    <verbatim|expression>, les d�rivations o� appara�t z�ro ou une fois une
    expression sont trait�es de fa�on s�par�e : avec <verbatim|runop>, puis
    <verbatim|lunop>, puis <verbatim|primary>. \ Certaines �rivations
    inutiles de la grammaire sont ainsi �vit�es : par exemple, dans
    <verbatim|expr-\<gtr\>ident> ou <verbatim|expr.ident>, <math|expr> ne
    peut pas se d�river en une assignation <verbatim|\<less\>e1\<gtr\> =
    \<less\>e2\<gtr\>> (� moins qu'elle soit entre parenth�ses), mais qu'en
    une expression "primaire" <verbatim|primary> (identificateur, this, NULL,
    constante, bool�en ou expression entre parenth�se), ce qui r�soud un
    certain nombre de conflits de la grammaire.

    <item><verbatim|cls_proto> �vite que la grammaire cr�e une d�rivation
    produisant l'appel d'une classe lors de la d�finition d'une autre. En
    effet, lors d'une telle d�finition, il faut rappeler que l'on ne doit pas
    avoir acc�s � d'autres classes externes.
  </itemize>

  Tous les tests fournis ont �t� v�rifi�s corrects.

  \;

  \;

  \;
</body>

<\initial>
  <\collection>
    <associate|language|french>
  </collection>
</initial>