OpenSigma
=========

What if we wanted to describe some data that we might have lying around
or acquire from somewhere?

Never mind how we *view* the data. Later, we might think of describing
a presentation for data as a spreadsheet or whatever. Let's just talk
about the structure of the data.

Let me just establish a syntactic convention.


Layout
------

I have a boringly simple approach to indentation-based layout. A line
subordinates the contiguous block of subsequent lines which are strictly
more indented.

Subordinated lines are treated as continuations of their headline unless
the headline ends with the layout herald, "-:". Note that

    this is the beginning of a headline
      and this is a continuation of the headline -:
        this line is subordinated to that headline
      and this is also subordinated to that headline
        but this line continues the second subordinate
      and this is a third subordinate

Of course, it's bad form to be ragged in that manner.


Classes
-------

A class is an extensible set of individuals. The point about being
individuals is to be mutally distinct places for information.
We proceed by attaching information to individuals.

I might want to say that there is such a thing as a student.

    class Student

I might want to say that individual students have certain information
attached: a unique email address and registration number, as well as
a human-name.

    for Student -:
      email ! String
      regNo ! String
      surname : String
      forename : String

The "for" declaration allows us to assert that information is available
for each individual in a class. We give <name> : <type> for the information,
but write <name> ! <type> when we expect each individual to have distinct
values for that information.

Students study modules (called "classes" in Strathclyde, but that could get
confusing). So that's a whole other class of individuals.

    class Module

No individual is both a Student and a Module.


Sigma in Disguise
-----------------

Classes are types, but not necessarily the other way around.

The comma operator forms a new type from two old types. E.g.,

    Student, Module

whose individuals are the *pairs* of students and modules.

The comma operator is really the type former for Sigma-types. You can name
the components if you like

    S : Student, M : Module

(idea: and you can reorder them, as long as the dependency graph is acyclic).

Anonymous components are none the less dependable-on.


Prop(ositions/erties)
---------------------

Some students study some modules.

    for Student, Module -:
      prop Studies

So what is "Studies"? It's a type which exists for each pair of
student and module, containing at most one inhabitant (whose existence
indicates that the student studies the module).

    Student, Module, Studies

is thus the class of *triples* consisting of a student, a module, and
the evidence that the student studies the module.

You can write "Studies" in any context with exactly one student and
one module.


Classes for Individuals
-----------------------

For each module, there will be some tests.

    for Module -:
      class Test

A test has a maximum possible score.

    for Module, Test -:
      maxPoss : {0..}

I should be able to write that by subordination

    for Module -:
      class Test
      for Test -:
        maxPoss : [0..]

which should be further contractible to

    for Module -:
      class Test -:
        maxPoss : [0..]

Each student studying a module might be present at one of that module's tests.
And if they were present, they have a score

    for Student, Module, Studies, Test -:
      prop Present -:
        score : [0..maxPoss]

I'm making this notation up as I go along, but I'm learning something.



For declarations
----------------

A declaration of form

    for <class> -:
      <decl>
      ...
      <decl>

tells us that for each individual in the class, the given declared things exist.

We always work relatively to an ambient class. At the top level, that's the
anonymous class with just one individual. The role of the `for` declaration is
to localize the ambient class.

What's really going on is functional programming.


Info declarations
-----------------

A declaration of the form

    <name> : <type>

tells us that each individual in the context has some information of the
given type with the given name.


Types
-----

We've had classes, properties and the Sigma construction. Let's also have

    String

(it's tempting to allow subtypes of String given by a grammar)

    Int

and we must have subtypes

    [i..]
    [..j]
    [i..j]

which are really just

    Int, (i <=)
    Int, (<= j)
    Int, (i <=), (<= j)

Let's have closed enumerations

    {tag1,..,tagn}

