sig Cancao {
	colaboradores: set Cantor
}

sig Album {
	cancoes: set Cancao
}

sig Cantor {
	albuns: set Album
}

sig Banda extends Cantor{}

sig Grammy {
	indicadosCantorBanda: set Cantor,
	indicadosAlbum: set Album,
	indicadosCancao: set Cancao,
	indicadosColaboracao: set Cancao
}

------------------------------------------------------ PREDICADOS ----------------------------------------------------------

-- Indicados a melhor cantor ou banda tem entre 4 e 8.
pred tamanhoCantorBanda[g:Grammy] {
	#listaCantoresBandas[g] >= 4 && #listaCantoresBandas[g]<= 8
}

-- Indicados a melhor album tem entre 4 e 8.
pred tamanhoAlbum[g:Grammy] {
	#listaAlbuns[g] >= 4 && #listaAlbuns[g] <= 8
}

-- Indicados a melhor cancao tem entre 4 e 8.
pred tamanhoCancao[g:Grammy] {
	#listaCancoes[g] >= 4 && #listaCancoes[g] <= 8
}

-- Indicados a melhor colaboracao tem entre 4 e 8.
pred tamanhoColaboracao[g:Grammy] {
	#listaColaboracoes[g] >= 4 && #listaColaboracoes[g] <= 8
}

-- Cantor/Banda passada esta concorrendo ao grammy passado.
pred cantorBandaIndicado[c:Cantor, g:Grammy] {
	c in listaCantoresBandas[g]
}

-- Ao menos um album do cantor/banda esta concorrendo a melhor album.
pred algumAlbumConcorrendo[c:Cantor, g:Grammy] {
	some listaAlbuns[c] & listaAlbuns[g]
}

-- Colaboracao passada esta concorrendo ao grammy passado.
pred colaboracaoIndicada[c:Cancao, g:Grammy] {
	c in listaColaboracoes[g]
}

-- A cancao tem mais que um colaborador.
pred variosColaboradores[c:Cancao] {
	#listaColaboradores[c] > 1
}

-- Album passado tem apenas um dono.
pred albumUmArtista[a:Album] {
	one a.~albuns
}

-- Album tem pelo menos uma cancao.
pred albumAoMenosUmaCancao[a:Album] {
	some a.cancoes
}

-- Cancao em um album.
pred cancaoUmAlbum[c:Cancao] {
	one c.~cancoes
}

-- O artista dono do album que possui a musica eh um dos colaboradores.
pred donoEhColaborador[c:Cancao] {
	some c.~cancoes.~albuns & c.colaboradores
}

------------------------------------------------------------- FUNCOES --------------------------------------------------------

-- Retorna a lista de albuns do cantor/banda passado.
fun listaAlbuns[c:Cantor]: set Album {
	c.albuns
}

-- Retorna a lista de colaboradores da cancao passada.
fun listaColaboradores[c:Cancao]: set Cantor{
	c.colaboradores
}

-- Retorna a lista de cantores/bandas indicados ao grammy passado.
fun listaCantoresBandas[g:Grammy]: set Cantor {
	g.indicadosCantorBanda
}

-- Retorna a lista de albuns indicados ao grammy passado.
fun listaAlbuns[g:Grammy]: set Album {
	g.indicadosAlbum
}

-- Retorna a lista de cancoes indicadas ao grammy passado.
fun listaCancoes[g:Grammy]: set Cancao {
	g.indicadosCancao
}

-- Retorna a lista de cancoes indicadas a melhor colaboracao no grammy passado.
fun listaColaboracoes[g:Grammy]: set Cancao {
	g.indicadosColaboracao
}

-- Retorna o numero das melhores cancoes que estao nos melhores albuns.
fun melhoresCancoesEmMelhoresAlbuns[g:Grammy]: Int {
	#{listaCancoes[g] & listaAlbuns[g].cancoes}
}

-- Retorna metade do numero de cancoes indicadas a melhor cancao.
fun metadeMelhoresCancoes[g:Grammy]: Int {
	div[#listaCancoes[g],2]
}

-------------------------------------------------------------- FATOS -----------------------------------------------------------

-- Existe apenas uma premiacao.
fact grammy{
	#Grammy = 1
}

-- Indicacoes com 4 a 8 indicados.
-- Todo cantor/Banda concorrente ao melhor cantor/banda tem um album concorrendo a melhor album.
fact indicadosCantorBanda {
	all g:Grammy | tamanhoCantorBanda[g]
	all g:Grammy, c:Cantor | cantorBandaIndicado[c,g]  => algumAlbumConcorrendo[c, g]
}

-- Indicacoes com 4 a 8 indicados.
fact indicadosAlbum {
	all g:Grammy | tamanhoAlbum[g]
}

-- Indicacoes com 4 a 8 indicados.
-- Pelo menos metade das cancoes indicadas devem ser cancoes 
-- que estao presentes em algum album indicado na categoria melhor album.
fact indicadosCancoes {
	all g:Grammy | tamanhoCancao[g]
	all g:Grammy | melhoresCancoesEmMelhoresAlbuns[g] >=  metadeMelhoresCancoes[g]
}

-- Indicacoes com 4 a 8 indicados.
-- Toda cancao concorrendo a melhor colaboracao tem mais que um colaborador.
fact indicadosColaboracoes {
	all g:Grammy | tamanhoColaboracao[g]
	all g:Grammy, c:Cancao | colaboracaoIndicada[c,g] => variosColaboradores[c]
}

-- Todo album pertence a apenas um artista.
-- Todo album possui ao menos uma cancao.
fact album {
	all a:Album | albumUmArtista[a]
	all a:Album | albumAoMenosUmaCancao[a]
}

-- Toda cancao pertece a apenas um album.
-- Toda cancao tem como colaborador o dono do album que a cancao pertence.
fact cancoes {
	all c:Cancao | cancaoUmAlbum[c]
	all c:Cancao | donoEhColaborador[c]
}

---------------------------------------------------------------ASSERTS----------------------------------------------------------

----------Grammy-----------

assert umGrammy{
	#Grammy = 1
}

----------CantorBandaIndicados----------

assert tamanhoIndicadosCantorBanda {
	all g:Grammy | #g.indicadosCantorBanda >= 4 && #g.indicadosCantorBanda <= 8
}

assert cantorBandaConcorrendoTemAlbumConcorrendo {
	all g:Grammy, c:Cantor | cantorBandaIndicado[c,g]  => algumAlbumConcorrendo[c, g]
}

----------AlbunsIndicados----------

assert tamanhoIndicadosAlbum {
	all g:Grammy | #g.indicadosAlbum>= 4 && #g.indicadosAlbum <= 8
}

----------CancoesIndicados----------

assert tamanhoIndicadosCancao {
	all g:Grammy | #g.indicadosCancao>= 4 && #g.indicadosCancao<= 8
}

assert metadeMelhoresCancoesEmMelhoresAlbuns{
	all g:Grammy | melhoresCancoesEmMelhoresAlbuns[g] >=  metadeMelhoresCancoes[g]
}

-----------ColaboracoesIndicados----------

assert tamanhoIndicadosColaboracao {
	all g:Grammy | #g.indicadosColaboracao>= 4 && #g.indicadosColaboracao<= 8
}

assert colaboracaoTemVariosColaboradores{
	all g:Grammy, c:Cancao | colaboracaoIndicada[c,g] => variosColaboradores[c]
}

----------Album----------

assert albumTemUmArtista{
	all a:Album | one a.~albuns
}

assert albumComAlgumaCancao{
	all a:Album | some a.cancoes
}

----------Cancao----------

assert  cancaoTemUmAlbum{
	all c:Cancao | one c.~cancoes
}

assert donoEhColaborador{
	all c:Cancao | some c.~cancoes.~albuns & c.colaboradores
}

-------------------------------------------------------------EXECUCAO----------------------------------------------------------
pred show{}
run show for 10

--------------------------------------------------------EXECUCAO ASSERTS-------------------------------------------------------
check umGrammy
check tamanhoIndicadosCantorBanda
check cantorBandaConcorrendoTemAlbumConcorrendo
check  tamanhoIndicadosCantorBanda
check tamanhoIndicadosCancao
check metadeMelhoresCancoesEmMelhoresAlbuns
check tamanhoIndicadosColaboracao
check colaboracaoTemVariosColaboradores
check albumTemUmArtista
check albumComAlgumaCancao
check cancaoTemUmAlbum
check donoEhColaborador
