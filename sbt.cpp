#include <iostream>
#include <vector>
#include <unordered_map>

using namespace std;

vector<int> depths;
int max_depth=-1;

struct node {
        int value;
        node* left;
        node* right;
        node(int v){
                value = v;
                left = NULL;
                right = NULL;
        }
};

void getDepths(node* t,int level){
        depths.push_back(level);
        if(level>max_depth)
                max_depth=level;
        if(t->left!=NULL)
                getDepths(t->left,level+1);
        if(t->right!=NULL)
                getDepths(t->right,level+1);
}

int main(){
        node tree(3);
        getDepths(&tree,0);
        unordered_map<int,int> ht;
        for(int i = 0; i < depths.size(); i++)
                ht[depths[i]]=0;
        for(int i = 0; i< depths.size(); i++) {
                ht[depths[i]]++;
        }

        bool flag = true;
        for(int i = 0; i < max_depth-1; i++) {
                if(ht[i]!=pow(2,i)) {
                        flag = false;
                        break;
                }
        }
        if(flag)
                cout<<"SUPERBALANCED TREE"<<endl;
        else
                cout<<"NOT A SUPERBALANCED TREE"<<endl;
        return 0;
}
