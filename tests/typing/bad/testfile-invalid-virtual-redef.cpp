class A {
    public:
    virtual int f(int x);
};

class B : public A {
    public:
    virtual void f(int x);
};

int main() {}
