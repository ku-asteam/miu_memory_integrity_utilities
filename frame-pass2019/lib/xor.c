#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

typedef struct NodeT{
    int data;
    struct NodeT * p;
}Node;

void insert (Node * hd, int data)
{
    Node * node= malloc(sizeof(Node));
    node->data= data;
     
    if (!hd) {
        hd= node;
        node->p= NULL; //prev and next are null
        return;
    }
    if (!hd->p) {
        hd->p= node;
        node->p= hd; 
        return;
    }
    
    Node * current= hd->p; //   
    Node * prev= NULL;
    
    while(true) {
        Node * next= current->p ^ prev; 
        
        if (!next) {
            break;
        }
        prev= current;
        current= next; 
    }
    node->p= current; 
    current->p= current->p ^ node;    

}

void printfNode(Node * hd)
{
    if (!hd) {
        printf("empty list\n");
        return;
    }
    Node * prev= NULL;
    Node * current= hd;
    
    while (true) {
        
        printf("%d\n", hd->data);

        Node * next= current->p ^ prev;
        
        if (!next) {
            break;    
        }
        prev= current;
        current= next;   
    }
}

int main (int argc, char ** argv)
{
    Node * hd= NULL;
    
    insert (hd, 0); 
    insert (hd, 1); 
    insert (hd, 2); 
    insert (hd, 3); 
    insert (hd, 4); 
   
    printNodes(hd);  
    return 0;
}
