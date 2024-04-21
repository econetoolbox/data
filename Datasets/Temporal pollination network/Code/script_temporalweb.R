library(igraph)

#load the data: example for the network in 2006
web<-read.table(file="interactions_2006.txt",sep="\t",header=TRUE)

#incidence matrix (web)
plantnames<-web[,1]
web<-as.matrix(web[,-1])
rownames(web)<-plantnames
web
g<-graph_from_biadjacency_matrix(web,weighted=TRUE)
