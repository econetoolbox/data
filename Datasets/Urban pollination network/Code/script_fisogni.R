library(bipartite)
library(igraph)

network<-read.table("Fisogni-et-al.2021_Dataset.txt",header=T,sep="\t")

#omit missing values
network<-na.omit(network)

##------------------------ ##
# Network preparation #
## ----------------------- ##

##cut the data set
#One total network (all season) per urbanisation class
network_low<-subset(network, urban=="low")
network_medium<-subset(network, urban=="medium")
network_high<-subset(network, urban=="high")
#One monthly network per urbanisation class
network_low1<-network[network$urban == "low" & network$visit %in% c(1,2),]
network_low2<-network[network$urban == "low" & network$visit %in% c(3,4),]
network_low3<-network[network$urban == "low" & network$visit %in% c(5,6),]
network_medium1<-network[network$urban == "medium" & network$visit %in% c(1,2),]
network_medium2<-network[network$urban == "medium" & network$visit %in% c(3,4),]
network_medium3<-network[network$urban == "medium" & network$visit %in% c(5,6),]
network_high1<-network[network$urban == "high" & network$visit %in% c(1,2),]
network_high2<-network[network$urban == "high" & network$visit %in% c(3,4),]
network_high3<-network[network$urban == "high" & network$visit %in% c(5,6),]

###function to create a graph
my.graph.fun<-function(el){
  mat<-as.matrix(el,dim(el)[1],2)
  mat.mod<-as.matrix(cbind(sapply(mat[,10],FUN = function(x) paste0("I_",x)),sapply(mat[,9],FUN = function(x) paste0("P_",x))))
  graph_from_edgelist(mat.mod,directed=F)
}

###function to create an incidence matrix -> apply to (.txt)
my.incidence<-function(gr){
  adj<-as.data.frame(as.matrix(as_adjacency_matrix(gr)))
  adj<-adj[order(names(adj)),order(names(adj))]
  I.index<-max(grep("I_",names(adj)))
  adj[1:I.index,(I.index+1):length(names(adj))]
}

#create incidence matrix
n_tot=my.incidence(my.graph.fun(network))
n_low=my.incidence(my.graph.fun(network_low))
n_medium=my.incidence(my.graph.fun(network_medium))
n_high=my.incidence(my.graph.fun(network_high))

n_low1=my.incidence(my.graph.fun(network_low1))
n_low2=my.incidence(my.graph.fun(network_low2))
n_low3=my.incidence(my.graph.fun(network_low3))
n_medium1=my.incidence(my.graph.fun(network_medium1))
n_medium2=my.incidence(my.graph.fun(network_medium2))
n_medium3=my.incidence(my.graph.fun(network_medium3))
n_high1=my.incidence(my.graph.fun(network_high1))
n_high2=my.incidence(my.graph.fun(network_high2))
n_high3=my.incidence(my.graph.fun(network_high3))


