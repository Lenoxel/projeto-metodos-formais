abstract sig Permissao {}

one sig Leitura, EscritaLeitura, Dono extends Permissao {} 

-- Todo objeto (arquivo ou diretorio) define um unico tipo de permissao para todos os usuarios, um unico tipo de permissao para usuarios externos e um unico tipo de permissao para usuarios locais
abstract sig Objeto {
	todos: one Permissao,
	externo: one Permissao,
	local: one Permissao -- Neste Computador
}

sig Arquivo extends Objeto {}

abstract sig Diretorio extends Objeto {
	conteudo: set Objeto -- Todo diretorio tem um conjunto de objetos, o que significa que todo diretorio pode ter arquivos e diretorios dentro dele
}

one sig Root extends Diretorio {}

sig Pasta extends Diretorio {
	pai: one Diretorio -- equivalente ao "/.." ?
}

abstract sig TipoDoUsuario {}

one sig Local, Externo extends TipoDoUsuario {} 

sig Usuario {
	permissoes: set Objeto,
	tipo: one TipoDoUsuario
}

fact {
	no pasta: Pasta | Root in pasta.conteudo -- nenhuma pasta contem Root
	all arquivo: Arquivo | arquivo in Diretorio.conteudo -- todo arquivo esta dentro de algum diretorio
	all pasta: Pasta | Root in pasta.^pai -- Todas as pastas estao no nivel inferior a Root
	no objeto: Objeto | objeto in objeto.^conteudo or objeto in objeto.^pai -- O conteudo de um diretorio nunca pode apontar para ele mesmo ate o ultimo conteudo. Do mesmo modo, o pai de uma pasta nunca pode apontar para ela mesma ate o ultimo diretorio pai
	all objeto: Objeto | objeto.^conteudo != objeto.^pai -- O conteudo de uma pasta nunca pode apontar para o seu diretorio pai
	all objeto: Objeto | garantirHiereaquiaDePermissoes[objeto]
	
	all permissao: Permissao | permissao in Objeto.todos or permissao in Objeto.externo or permissao in Objeto.local -- Toda permissao criada no modelo precisa estar relacionada a um objeto
	
	all usuario: Usuario | some usuario.permissoes -- Todo usuario criado no modelo precisa ter alguma permissao para alguma pasta, arquivo ou diretorio
	all tipoDoUsuario: TipoDoUsuario | tipoDoUsuario in Usuario.tipo -- Todo tipoDoUsuario criado no modelo precisa estar relacionado a um Usuario
}

-- Um arquivo nunca pode ter, para uma determinada categoria de usuarios, uma permissao menos restrita do que um diretorio ancestral dele.
pred garantirHiereaquiaDePermissoes(objeto: Objeto) {
	no objeto: Objeto | 
	(objeto.~conteudo.todos = Leitura and (objeto.todos = EscritaLeitura or objeto.todos = Dono))
	or
	(objeto.~conteudo.todos = EscritaLeitura and (objeto.todos = Dono))
	or
	(objeto.~conteudo.externo = Leitura and (objeto.externo = EscritaLeitura or objeto.externo = Dono))
	or
	(objeto.~conteudo.externo = EscritaLeitura and (objeto.externo = Dono))
	or
	(objeto.~conteudo.local = Leitura and (objeto.local = EscritaLeitura or objeto.local = Dono))
	or
	(objeto.~conteudo.local = EscritaLeitura and (objeto.local = Dono))
}

---------------

pred test {
	some Objeto
}

run test for 10
